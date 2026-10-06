import RealRooted.SymmetricDecomposition.FPolynomialInterlacing

/-!
# `I_d` and `R_d` symmetric decompositions

Formula, existence, uniqueness, and compatibility results for the two
Brändén--Solus symmetric decompositions.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

lemma eval_one_idTransform {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (idTransform d p).eval 1 = p.eval 1 := by
  let : Invertible (1 : ℝ) := invertibleOne
  simpa [idTransform, one_pow] using
    (Polynomial.eval₂_reflect_mul_pow (i := RingHom.id ℝ) (x := (1 : ℝ)) d p hd)

lemma X_sub_one_dvd_sub_idTransform {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    X - 1 ∣ p - idTransform d p := by
  simp [show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp, Polynomial.dvd_iff_isRoot,
    Polynomial.IsRoot.def, eval_one_idTransform hd]

lemma X_sub_one_dvd_X_mul_idTransform_sub {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    X - 1 ∣ X * idTransform d p - p := by
  simp [show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp, Polynomial.dvd_iff_isRoot,
    Polynomial.IsRoot.def, eval_one_idTransform hd]

lemma idDecompositionBFormula_mul_X_sub_one {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (X - 1) * idDecompositionBFormula d p = p - idTransform d p := by
  have hdvd : (p - idTransform d p) %ₘ (X - 1) = 0 := by
    rw [show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp]
    rw [Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_sub_C (1 : ℝ))]
    exact X_sub_one_dvd_sub_idTransform hd
  have h := Polynomial.modByMonic_add_div (p - idTransform d p) (X - 1)
  rw [hdvd, zero_add] at h
  simpa [idDecompositionBFormula] using h

lemma idDecompositionAFormula_mul_X_sub_one {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (X - 1) * idDecompositionAFormula d p = X * idTransform d p - p := by
  have hdvd : (X * idTransform d p - p) %ₘ (X - 1) = 0 := by
    rw [show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp]
    rw [Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_sub_C (1 : ℝ))]
    exact X_sub_one_dvd_X_mul_idTransform_sub hd
  have h := Polynomial.modByMonic_add_div (X * idTransform d p - p) (X - 1)
  rw [hdvd, zero_add] at h
  simpa [idDecompositionAFormula] using h

lemma idTransform_natDegree_le {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (idTransform d p).natDegree ≤ d :=
  (Polynomial.natDegree_reflect_le (N := d) (p := p)).trans <| max_le le_rfl hd

lemma idTransform_succ {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    idTransform (d + 1) p = X * idTransform d p := by
  simpa [idTransform, mul_comm, mul_left_comm, mul_assoc] using
    (Polynomial.reflect_mul (f := p) (g := (1 : ℝ[X])) (F := d) (G := 1) hd
      (show (1 : ℝ[X]).natDegree ≤ 1 by simp))

lemma idTransform_X_mul_succ {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    idTransform (d + 1) (X * p) = idTransform d p := by
  simpa [idTransform, add_comm] using
    (Polynomial.reflect_mul (f := (X : ℝ[X])) (g := p) (F := 1) (G := d)
      Polynomial.natDegree_X_le hd)

lemma idTransform_of_natDegree_le_pred {d : ℕ} (hd : 0 < d) {p : ℝ[X]}
    (hp : p.natDegree ≤ d - 1) :
    idTransform d p = X * idTransform (d - 1) p := by
  cases d with
  | zero =>
      lia
  | succ n =>
      simpa using (idTransform_succ (d := n) (p := p) hp)

lemma idTransform_X_mul_of_natDegree_le_pred {d : ℕ} (hd : 0 < d) {p : ℝ[X]}
    (hp : p.natDegree ≤ d - 1) :
    idTransform d (X * p) = idTransform (d - 1) p := by
  cases d with
  | zero =>
      lia
  | succ n =>
      simpa using (idTransform_X_mul_succ (d := n) (p := p) hp)

lemma idTransform_X_sub_one :
    idTransform 1 (X - 1 : ℝ[X]) = -(X - 1) := by
  simp [idTransform, sub_eq_add_neg, add_comm]

lemma coeff_zero_eq_zero_of_idTransform_fixed_of_natDegree_lt {d : ℕ} {p : ℝ[X]}
    (hfix : idTransform d p = p) (hdeg : p.natDegree < d) :
    p.coeff 0 = 0 := by
  have hcoeff : p.coeff 0 = p.coeff d := by
    simpa [idTransform, Polynomial.coeff_reflect, Polynomial.revAt_zero] using
      (congrArg (fun q => q.coeff 0) hfix).symm
  exact hcoeff.trans (Polynomial.coeff_eq_zero_of_natDegree_lt hdeg)

lemma isRoot_zero_of_idTransform_fixed_of_natDegree_lt {d : ℕ} {p : ℝ[X]}
    (hfix : idTransform d p = p) (hdeg : p.natDegree < d) :
    p.IsRoot 0 := by
  rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero]
  exact coeff_zero_eq_zero_of_idTransform_fixed_of_natDegree_lt hfix hdeg

lemma exists_eq_X_mul_of_idTransform_fixed_of_natDegree_lt {d : ℕ} {p : ℝ[X]}
    (hfix : idTransform d p = p) (hdeg : p.natDegree < d) :
    ∃ q, p = X * q ∧ idTransform (d - 2) q = q := by
  cases d with
  | zero =>
      lia
  | succ d =>
      cases d with
      | zero =>
          have hpdeg : p.natDegree ≤ 0 := by lia
          have hp0 : p = 0 := by
            calc
              p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hpdeg
              _ = 0 := by simp [coeff_zero_eq_zero_of_idTransform_fixed_of_natDegree_lt hfix hdeg]
          simp_all
      | succ n =>
          have hroot0 : p.IsRoot 0 :=
            isRoot_zero_of_idTransform_fixed_of_natDegree_lt hfix hdeg
          obtain ⟨q, hq0⟩ := dvd_iff_isRoot.mpr hroot0
          have hq : p = X * q := by simp_all
          have hqdeg : q.natDegree ≤ n := by
            by_cases hqz : q = 0
            · simp [hqz]
            · simp_all
          have hqdeg' : q.natDegree ≤ n + 1 := le_trans hqdeg (Nat.le_succ _)
          have hstep1 : idTransform (n + 2) (X * q) = idTransform (n + 1) q := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (idTransform_X_mul_succ (d := n + 1) (p := q) hqdeg')
          have hstep2 : idTransform (n + 1) q = X * idTransform n q := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (idTransform_of_natDegree_le_pred (d := n + 1) (Nat.succ_pos _) hqdeg)
          simp_all

theorem isIdDecomposition_descend_of_lt_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : 2 ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_lt : a.natDegree < d)
    (hb_lt : b.natDegree < d - 1) :
    ∃ a' b', a = X * a' ∧ b = X * b' ∧
      p = X * (a' + X * b') ∧
      IsIdDecomposition (d - 2) (a' + X * b') a' b' := by
  rcases hid with ⟨hp_eq, ha_deg, hb_deg, hfixA, hfixB⟩
  obtain ⟨a', haX, hfixA'⟩ :=
    exists_eq_X_mul_of_idTransform_fixed_of_natDegree_lt hfixA ha_lt
  obtain ⟨b', hbX, hfixB'⟩ :=
    exists_eq_X_mul_of_idTransform_fixed_of_natDegree_lt hfixB hb_lt
  have ha'deg : a'.natDegree ≤ d - 2 := by
    by_cases ha'0 : a' = 0
    · simp [ha'0]
    · rw [haX, natDegree_X_mul ha'0] at ha_lt
      lia
  have hb'deg : b'.natDegree ≤ d - 3 := by
    by_cases hb'0 : b' = 0
    · simp [hb'0]
    · rw [hbX, natDegree_X_mul hb'0] at hb_lt
      lia
  have hpX : p = X * (a' + X * b') := by grind
  have hsub : (d - 2) - 1 = d - 3 := by lia
  refine ⟨a', b', haX, hbX, hpX, ?_⟩
  refine ⟨rfl, ha'deg, ?_, hfixA', ?_⟩ <;> lia

lemma idTransform_X_mul_of_natDegree_le_two_pred {d : ℕ} {p : ℝ[X]}
    (hd : 2 ≤ d) (hp : p.natDegree ≤ d - 2) :
    idTransform d (X * p) = X * idTransform (d - 2) p := by
  calc
    idTransform d (X * p) = idTransform (d - 1) p :=
      idTransform_X_mul_of_natDegree_le_pred (by lia) (by lia)
    _ = X * idTransform (d - 2) p :=
      idTransform_of_natDegree_le_pred (d := d - 1) (by lia) (by lia)

theorem strictInterl_iff_strictInterl_mul_X_both_of_hasNonnegCoeffs {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    StrictInterl f g ↔ StrictInterl (X * f) (X * g) := by
  constructor
  · intro h
    have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs h.1.2 hfnn
    have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs h.2.1.2 hgnn
    exact (StrictInterl.mul_X_both_iff_of_roots_nonpos hf_nonpos hg_nonpos).1 h
  · intro h
    have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_X_mul h.1.1 h.1.2
    have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_X_mul h.2.1.1 h.2.1.2
    have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf_rr.2 hfnn
    have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hg_rr.2 hgnn
    exact (StrictInterl.mul_X_both_iff_of_roots_nonpos hf_nonpos hg_nonpos).2 h

lemma hasNonnegCoeffs_of_eq_X_mul {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (h : p = X * q) :
    HasNonnegCoeffs q := by
  intro n
  simpa [h, Polynomial.coeff_X_mul] using hp (n + 1)

lemma natDegree_idDecompositionBFormula_le {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (idDecompositionBFormula d p).natDegree ≤ d - 1 := by
  have hnum : (p - idTransform d p).natDegree ≤ d := by
    simpa using Polynomial.natDegree_sub_le_of_le hd (idTransform_natDegree_le hd)
  rw [idDecompositionBFormula, show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp]
  rw [Polynomial.natDegree_divByMonic_X_sub_C]
  lia

lemma natDegree_idDecompositionAFormula_le {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (idDecompositionAFormula d p).natDegree ≤ d := by
  have hI : (idTransform d p).natDegree ≤ d := idTransform_natDegree_le hd
  have hXI : (X * idTransform d p).natDegree ≤ d + 1 := by
    simpa [add_comm] using
      (Polynomial.natDegree_mul_le_of_le Polynomial.natDegree_X_le hI)
  have hp' : p.natDegree ≤ d + 1 := le_trans hd (Nat.le_succ d)
  have hnum : (X * idTransform d p - p).natDegree ≤ d + 1 := by
    simpa using Polynomial.natDegree_sub_le_of_le hXI hp'
  rw [idDecompositionAFormula, show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp]
  rw [Polynomial.natDegree_divByMonic_X_sub_C]
  lia

theorem idDecompositionFormula_eq_add_X_mul {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    p = idDecompositionAFormula d p + X * idDecompositionBFormula d p := by
  have hA := idDecompositionAFormula_mul_X_sub_one hd
  have hB := idDecompositionBFormula_mul_X_sub_one hd
  have hstep :
    (X - 1) * (idDecompositionAFormula d p + X * idDecompositionBFormula d p)
        = (X - 1) * idDecompositionAFormula d p + X * ((X - 1) * idDecompositionBFormula d p) := by
            ring
  have hmul :
      (X - 1) * (idDecompositionAFormula d p + X * idDecompositionBFormula d p) = (X - 1) * p := by
    grind
  have hdiv := congrArg (fun q => q /ₘ (X - 1)) hmul
  rw [show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp] at hdiv
  have hleft_cancel :
      ((X - C (1 : ℝ)) * (idDecompositionAFormula d p + X * idDecompositionBFormula d p)) /ₘ
          (X - C (1 : ℝ)) =
        idDecompositionAFormula d p + X * idDecompositionBFormula d p := by
    simpa using
      (Polynomial.mul_divByMonic_cancel_left
        (idDecompositionAFormula d p + X * idDecompositionBFormula d p)
        (Polynomial.monic_X_sub_C (1 : ℝ)))
  have hright_cancel :
      ((X - C (1 : ℝ)) * p) /ₘ (X - C (1 : ℝ)) = p := by
    simpa using
      (Polynomial.mul_divByMonic_cancel_left p (Polynomial.monic_X_sub_C (1 : ℝ)))
  lia

theorem idDecompositionFormula_idTransform_eq_add {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    idTransform d p = idDecompositionAFormula d p + idDecompositionBFormula d p := by
  have hB := idDecompositionBFormula_mul_X_sub_one hd
  calc
    idTransform d p = p - (p - idTransform d p) := by simp
    _ = p - (X - 1) * idDecompositionBFormula d p := by lia
    _ =
        (idDecompositionAFormula d p + X * idDecompositionBFormula d p) -
          (X - 1) * idDecompositionBFormula d p := by
            nth_rw 1 [idDecompositionFormula_eq_add_X_mul hd]
    _ = idDecompositionAFormula d p + idDecompositionBFormula d p := by grind

theorem idDecompositionFormula_eq_of_system {d : ℕ} {p a b : ℝ[X]} (hd : p.natDegree ≤ d)
    (hp : p = a + X * b) (hI : idTransform d p = a + b) :
    a = idDecompositionAFormula d p ∧ b = idDecompositionBFormula d p := by
  have hsub : p - idTransform d p = (X - 1) * b := by grind
  have hdiv := congrArg (fun q => q /ₘ (X - 1)) hsub
  rw [show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp] at hdiv
  have hb' : idDecompositionBFormula d p = b := by
    have hcancel : ((X - C (1 : ℝ)) * b) /ₘ (X - C (1 : ℝ)) = b := by
      simpa using
        (Polynomial.mul_divByMonic_cancel_left b (Polynomial.monic_X_sub_C (1 : ℝ)))
    calc
      idDecompositionBFormula d p = (p - idTransform d p) /ₘ (X - C (1 : ℝ)) := by
        simp [idDecompositionBFormula]
      _ = ((X - C (1 : ℝ)) * b) /ₘ (X - C (1 : ℝ)) := hdiv
      _ = b := hcancel
  have hb : b = idDecompositionBFormula d p := hb'.symm
  refine ⟨?_, hb⟩
  calc
    a = p - X * b := by grind
    _ = p - X * idDecompositionBFormula d p := by lia
    _ = idDecompositionAFormula d p := by
      nth_rw 1 [idDecompositionFormula_eq_add_X_mul hd]
      ring

lemma idDecompositionBFormula_fixed {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    idTransform (d - 1) (idDecompositionBFormula d p) = idDecompositionBFormula d p := by
  cases d with
  | zero =>
      have hp0 : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hd
      have hI0 : idTransform 0 p = p := by
        rw [hp0, idTransform, Polynomial.reflect_C]
        lia
      rw [idDecompositionBFormula, hI0, sub_self, zero_divByMonic]
      simp
  | succ n =>
      let a := idDecompositionAFormula (n + 1) p
      let b := idDecompositionBFormula (n + 1) p
      have ha : p = a + X * b := by
        simpa [a, b] using idDecompositionFormula_eq_add_X_mul (d := n + 1) hd
      have hI : idTransform (n + 1) p = a + b := by
        simpa [a, b] using idDecompositionFormula_idTransform_eq_add (d := n + 1) hd
      have hbdeg : b.natDegree ≤ n := by
        simpa [b] using natDegree_idDecompositionBFormula_le (d := n + 1) hd
      have ha' : p = idTransform (n + 1) a + X * idTransform n b := by
        have h0 : p = idTransform (n + 1) a + idTransform (n + 1) b := by
          simpa [idTransform, Polynomial.reflect_add, a, b] using
            (congrArg (idTransform (n + 1)) hI)
        rw [idTransform_of_natDegree_le_pred (d := n + 1) (Nat.succ_pos _) hbdeg] at h0
        lia
      have hI' : idTransform (n + 1) p = idTransform (n + 1) a + idTransform n b := by
        have h0 : idTransform (n + 1) p = idTransform (n + 1) a + idTransform (n + 1) (X * b) := by
          simp_all
        rw [idTransform_X_mul_of_natDegree_le_pred (d := n + 1) (Nat.succ_pos _) hbdeg] at h0
        lia
      have hsys := idDecompositionFormula_eq_of_system (d := n + 1) (p := p) hd ha' hI'
      lia

lemma idDecompositionAFormula_fixed {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    idTransform d (idDecompositionAFormula d p) = idDecompositionAFormula d p := by
  cases d with
  | zero =>
      have hp0 : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hd
      have hI0 : idTransform 0 p = p := by
        rw [hp0, idTransform, Polynomial.reflect_C]
        lia
      have hB0 : idDecompositionBFormula 0 p = 0 := by
        rw [idDecompositionBFormula, hI0, sub_self, zero_divByMonic]
      have hA0 : idDecompositionAFormula 0 p = p := by
        simpa [hB0] using (idDecompositionFormula_eq_add_X_mul (d := 0) hd).symm
      lia
  | succ n =>
      let a := idDecompositionAFormula (n + 1) p
      let b := idDecompositionBFormula (n + 1) p
      have ha : p = a + X * b := by
        simpa [a, b] using idDecompositionFormula_eq_add_X_mul (d := n + 1) hd
      have hI : idTransform (n + 1) p = a + b := by
        simpa [a, b] using idDecompositionFormula_idTransform_eq_add (d := n + 1) hd
      have hbdeg : b.natDegree ≤ n := by
        simpa [b] using natDegree_idDecompositionBFormula_le (d := n + 1) hd
      have ha' : p = idTransform (n + 1) a + X * idTransform n b := by
        have h0 : p = idTransform (n + 1) a + idTransform (n + 1) b := by
          simpa [idTransform, Polynomial.reflect_add, a, b] using
            (congrArg (idTransform (n + 1)) hI)
        rw [idTransform_of_natDegree_le_pred (d := n + 1) (Nat.succ_pos _) hbdeg] at h0
        lia
      have hI' : idTransform (n + 1) p = idTransform (n + 1) a + idTransform n b := by
        have h0 : idTransform (n + 1) p = idTransform (n + 1) a + idTransform (n + 1) (X * b) := by
          simp_all
        rw [idTransform_X_mul_of_natDegree_le_pred (d := n + 1) (Nat.succ_pos _) hbdeg] at h0
        lia
      have hsys := idDecompositionFormula_eq_of_system (d := n + 1) (p := p) hd ha' hI'
      lia

theorem isIdDecomposition_formula {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    IsIdDecomposition d p (idDecompositionAFormula d p) (idDecompositionBFormula d p) := by
  refine ⟨idDecompositionFormula_eq_add_X_mul hd, natDegree_idDecompositionAFormula_le hd,
    natDegree_idDecompositionBFormula_le hd, idDecompositionAFormula_fixed hd,
    idDecompositionBFormula_fixed hd⟩

/-- Brändén--Solus Lemma 2.1: every polynomial of degree at most `d` has a
unique symmetric `I_d`-decomposition, and the explicit formulas agree with the
abstract pair. -/
theorem idDecompositionExistsUnique {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    ∃! ab : ℝ[X] × ℝ[X],
      IsIdDecomposition d p ab.1 ab.2 ∧
      ab.1 = idDecompositionAFormula d p ∧
      ab.2 = idDecompositionBFormula d p := by
  refine ⟨⟨idDecompositionAFormula d p, idDecompositionBFormula d p⟩, ?_, ?_⟩
  · exact ⟨isIdDecomposition_formula hd, rfl, rfl⟩
  · lia

@[simp] lemma rdTransform_zero (d : ℕ) :
    rdTransform d (0 : ℝ[X]) = 0 := by
  simp [rdTransform]

@[simp] lemma rdTransform_add (d : ℕ) (p q : ℝ[X]) :
    rdTransform d (p + q) = rdTransform d p + rdTransform d q := by
  simp [rdTransform, mul_add]

@[simp] lemma rdTransform_neg (d : ℕ) (p : ℝ[X]) :
    rdTransform d (-p) = -rdTransform d p := by
  simp [rdTransform]

@[simp] lemma rdTransform_sub (d : ℕ) (p q : ℝ[X]) :
    rdTransform d (p - q) = rdTransform d p - rdTransform d q := by
  simp [sub_eq_add_neg]

lemma rdTransform_succ (d : ℕ) (p : ℝ[X]) :
    rdTransform (d + 1) p = -rdTransform d p := by
  unfold rdTransform
  grind

lemma rdTransform_involutive (d : ℕ) (p : ℝ[X]) :
    rdTransform d (rdTransform d p) = p := by
  unfold rdTransform
  rw [mul_comp, C_comp, comp_assoc]
  have hcomp : (-X - 1 : ℝ[X]).comp (-X - 1) = X := by simp
  rw [hcomp, ← mul_assoc, ← map_mul]
  have hpow : ((-1 : ℝ) ^ d) * ((-1 : ℝ) ^ d) = 1 := by
    rw [← pow_add, ← two_mul]
    norm_num
  simp_all

lemma rdTransform_X_mul_succ (d : ℕ) (p : ℝ[X]) :
    rdTransform (d + 1) (X * p) = (X + 1) * rdTransform d p := by
  rw [rdTransform_succ, rdTransform, mul_comp, X_comp]
  calc
    -(C (((-1 : ℝ) ^ d)) * ((-X - 1) * p.comp (-X - 1)))
        = (X + 1) * (C (((-1 : ℝ) ^ d)) * p.comp (-X - 1)) := by ring
    _ = (X + 1) * rdTransform d p := by rw [rdTransform]

lemma rdTransform_X_add_one_mul_succ (d : ℕ) (p : ℝ[X]) :
    rdTransform (d + 1) ((X + 1) * p) = X * rdTransform d p := by
  rw [show ((X + 1) * p : ℝ[X]) = X * p + p by grind]
  rw [rdTransform_add, rdTransform_X_mul_succ, rdTransform_succ]
  ring

lemma rdTransform_basis_term (d n : ℕ) (a : ℝ) (hn : n ≤ d) :
    rdTransform d (C a * X ^ n * (X + 1) ^ (d - n)) = C a * X ^ (d - n) * (X + 1) ^ n := by
  induction d generalizing n with
  | zero =>
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
      subst hn0
      simp [rdTransform]
  | succ d ih =>
      cases n with
      | zero =>
          have hzero :
              C a * X ^ 0 * (X + 1) ^ (d + 1 - 0) = (X + 1) * (C a * X ^ 0 * (X + 1) ^ d) := by
            grind
          calc
            rdTransform (d + 1) (C a * X ^ 0 * (X + 1) ^ (d + 1 - 0))
                = rdTransform (d + 1) ((X + 1) * (C a * X ^ 0 * (X + 1) ^ d)) := by lia
            _ = X * rdTransform d (C a * X ^ 0 * (X + 1) ^ d) := by
                  rw [rdTransform_X_add_one_mul_succ]
            _ = X * (C a * X ^ (d - 0) * (X + 1) ^ 0) := by
                  simpa using congrArg (fun q => X * q) (ih 0 (Nat.zero_le d))
            _ = C a * X ^ (d + 1 - 0) * (X + 1) ^ 0 := by grind
      | succ n =>
          have hn' : n ≤ d := Nat.succ_le_succ_iff.mp hn
          have hsucc :
              C a * X ^ (n + 1) * (X + 1) ^ (d + 1 - (n + 1)) =
                X * (C a * X ^ n * (X + 1) ^ (d - n)) := by
            grind
          calc
            rdTransform (d + 1) (C a * X ^ (n + 1) * (X + 1) ^ (d + 1 - (n + 1)))
                = rdTransform (d + 1) (X * (C a * X ^ n * (X + 1) ^ (d - n))) := by lia
            _ = (X + 1) * rdTransform d (C a * X ^ n * (X + 1) ^ (d - n)) := by
                  rw [rdTransform_X_mul_succ]
            _ = (X + 1) * (C a * X ^ (d - n) * (X + 1) ^ n) := by simp_all
            _ = C a * X ^ (d + 1 - (n + 1)) * (X + 1) ^ (n + 1) := by grind

lemma rdTransform_fPolynomial (d : ℕ) (h : ℝ[X]) :
    rdTransform d (fPolynomial d h) = fPolynomial d (idTransform d h) := by
  refine Polynomial.induction_on' h ?_ ?_
  · simp_all
  · intro n a
    by_cases hn : n ≤ d
    · have hf : fPolynomial d (monomial n a) = C a * X ^ n * (X + 1) ^ (d - n) := by
          simp [fPolynomial_monomial, hn]
      rw [hf, rdTransform_basis_term d n a hn]
      have hid : idTransform d (monomial n a) = monomial (d - n) a := by
        rw [idTransform, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.reflect_C_mul_X_pow]
        rw [Polynomial.revAt_le hn, Polynomial.C_mul_X_pow_eq_monomial]
      rw [hid]
      have hsub : d - (d - n) = n := by lia
      have hfd : fPolynomial d (monomial (d - n) a) = C a * X ^ (d - n) * (X + 1) ^ n := by
        have hle : d - n ≤ d := Nat.sub_le _ _
        simpa [hle, hsub] using (fPolynomial_monomial d (d - n) a)
      lia
    · have hgt : d < n := lt_of_not_ge hn
      have hf : fPolynomial d (monomial n a) = 0 := by simp [fPolynomial_monomial, hn]
      rw [hf, rdTransform_zero]
      have hid : idTransform d (monomial n a) = monomial n a := by
        rw [idTransform, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.reflect_C_mul_X_pow]
        rw [Polynomial.revAt_eq_self_of_lt hgt, Polynomial.C_mul_X_pow_eq_monomial]
      lia

lemma natDegree_rdTransform_eq (d : ℕ) (p : ℝ[X]) :
    (rdTransform d p).natDegree = p.natDegree := by
  have hX1 : (-X - 1 : ℝ[X]) = -(X + 1) := by ring
  have ht : (-X - 1 : ℝ[X]).natDegree = 1 := by
    rw [hX1, Polynomial.natDegree_neg, show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp,
      Polynomial.natDegree_X_add_C]
  unfold rdTransform
  rw [Polynomial.natDegree_C_mul (pow_ne_zero _ (by simp)), Polynomial.natDegree_comp, ht]
  lia

lemma leadingCoeff_rdTransform (d : ℕ) (p : ℝ[X]) :
    (rdTransform d p).leadingCoeff = (-1 : ℝ) ^ (d + p.natDegree) * p.leadingCoeff := by
  have hX1 : (-X - 1 : ℝ[X]) = -(X + 1) := by ring
  have hdeg : (-X - 1 : ℝ[X]).natDegree = 1 := by
    rw [hX1, Polynomial.natDegree_neg, show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp,
      Polynomial.natDegree_X_add_C]
  have ht : (-X - 1 : ℝ[X]).natDegree ≠ 0 := by lia
  have hl : (-X - 1 : ℝ[X]).leadingCoeff = (-1 : ℝ) := by
    rw [hX1, Polynomial.leadingCoeff_neg, show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp,
      Polynomial.leadingCoeff_X_add_C]
  unfold rdTransform
  rw [Polynomial.leadingCoeff_C_mul_of_isUnit (show IsUnit (((-1 : ℝ) ^ d)) by
        simp),
    Polynomial.leadingCoeff_comp ht, hl]
  grind

lemma leadingCoeff_rdTransform_eq_of_natDegree_eq {d : ℕ} {p : ℝ[X]} (hd : p.natDegree = d) :
    (rdTransform d p).leadingCoeff = p.leadingCoeff := by
  simp [leadingCoeff_rdTransform, hd, ← two_mul d, pow_mul]

theorem rdDecompositionFormula_eq_add_X_mul (d : ℕ) (p : ℝ[X]) :
    p = rdDecompositionAFormula d p + X * rdDecompositionBFormula d p := by
  unfold rdDecompositionAFormula rdDecompositionBFormula
  ring

theorem rdDecompositionFormula_rdTransform_eq_add_X_add_one_mul (d : ℕ) (p : ℝ[X]) :
    rdTransform d p = rdDecompositionAFormula d p + (X + 1) * rdDecompositionBFormula d p := by
  unfold rdDecompositionAFormula rdDecompositionBFormula
  ring

theorem rdDecompositionFormula_eq_of_system {d : ℕ} {p a b : ℝ[X]}
    (hp : p = a + X * b) (hR : rdTransform d p = a + (X + 1) * b) :
    a = rdDecompositionAFormula d p ∧ b = rdDecompositionBFormula d p := by
  have hbR : b = rdTransform d p - p := by grind
  have hb : b = rdDecompositionBFormula d p := by simpa [rdDecompositionBFormula] using hbR
  refine ⟨?_, hb⟩
  calc
    a = p - X * b := by grind
    _ = p - X * (rdTransform d p - p) := by lia
    _ = rdDecompositionAFormula d p := by
      unfold rdDecompositionAFormula
      ring

lemma natDegree_rdDecompositionBFormula_le {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (rdDecompositionBFormula d p).natDegree ≤ d - 1 := by
  have hR : (rdTransform d p).natDegree ≤ d := by
    rw [natDegree_rdTransform_eq]
    lia
  have hdeg : (rdDecompositionBFormula d p).natDegree ≤ d := by
    unfold rdDecompositionBFormula
    simpa using Polynomial.natDegree_sub_le_of_le hR hd
  rcases lt_or_eq_of_le hd with hlt | hEq
  · have hR' : (rdTransform d p).natDegree ≤ d - 1 := by
      rw [natDegree_rdTransform_eq]
      lia
    have hp' : p.natDegree ≤ d - 1 := by lia
    unfold rdDecompositionBFormula
    simpa using Polynomial.natDegree_sub_le_of_le hR' hp'
  · have hcoeff : (rdDecompositionBFormula d p).coeff d = 0 := by
      have hRdeg : (rdTransform d p).natDegree = d := by rw [natDegree_rdTransform_eq, hEq]
      have hRcoeff : (rdTransform d p).coeff d = p.leadingCoeff := by
        calc
          (rdTransform d p).coeff d = (rdTransform d p).leadingCoeff := by
            simpa [hRdeg] using (Polynomial.coeff_natDegree (p := rdTransform d p))
          _ = p.leadingCoeff := by rw [leadingCoeff_rdTransform_eq_of_natDegree_eq hEq]
      have hpcoeff : p.coeff d = p.leadingCoeff := by
        simpa [hEq] using (Polynomial.coeff_natDegree (p := p))
      unfold rdDecompositionBFormula
      simp_all
    exact Polynomial.natDegree_le_pred hdeg hcoeff

lemma natDegree_rdDecompositionAFormula_le {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    (rdDecompositionAFormula d p).natDegree ≤ d := by
  cases d with
  | zero =>
      have hp0 : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hd
      have hA0 : rdDecompositionAFormula 0 p = p := by
        rw [hp0, rdDecompositionAFormula]
        simp [rdTransform]
        ring
      lia
  | succ n =>
      have hbdeg : (rdDecompositionBFormula (n + 1) p).natDegree ≤ n :=
        by simpa using natDegree_rdDecompositionBFormula_le hd
      have hXb : (X * rdDecompositionBFormula (n + 1) p).natDegree ≤ n + 1 := by
        have hXb' :=
          Polynomial.natDegree_mul_le_of_le Polynomial.natDegree_X_le hbdeg
        lia
      have hA : rdDecompositionAFormula (n + 1) p =
          p - X * rdDecompositionBFormula (n + 1) p := by
        unfold rdDecompositionAFormula rdDecompositionBFormula
        ring
      rw [hA]
      simpa using Polynomial.natDegree_sub_le_of_le hd hXb

lemma rdDecompositionBFormula_fixed {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    rdTransform (d - 1) (rdDecompositionBFormula d p) = rdDecompositionBFormula d p := by
  cases d with
  | zero =>
      have hp0 : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hd
      rw [rdDecompositionBFormula, hp0]
      simp [rdTransform]
  | succ n =>
      have hpred : rdTransform n (rdTransform (n + 1) p) = -p := by
        rw [rdTransform_succ, rdTransform_neg, rdTransform_involutive]
      have hs : rdTransform n p = -rdTransform (n + 1) p := by
        rw [rdTransform_succ]
        simp
      change rdTransform n (rdTransform (n + 1) p - p) = rdTransform (n + 1) p - p
      rw [rdTransform_sub, hpred, hs]
      ring

lemma rdDecompositionAFormula_fixed {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    rdTransform d (rdDecompositionAFormula d p) = rdDecompositionAFormula d p := by
  cases d with
  | zero =>
      have hp0 : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hd
      have hB0 : rdDecompositionBFormula 0 p = 0 := by
        rw [rdDecompositionBFormula, hp0]
        simp [rdTransform]
      have hA0 : rdDecompositionAFormula 0 p = p := by
        simpa [hB0] using (rdDecompositionFormula_eq_add_X_mul 0 p).symm
      rw [hA0, hp0]
      simp [rdTransform]
  | succ n =>
      have hpred : rdTransform n (rdTransform (n + 1) p) = -p := by
        rw [rdTransform_succ, rdTransform_neg, rdTransform_involutive]
      have hs : rdTransform n p = -rdTransform (n + 1) p := by
        rw [rdTransform_succ]
        simp
      rw [rdDecompositionAFormula, rdTransform_sub, rdTransform_X_add_one_mul_succ,
        rdTransform_X_mul_succ, hpred, hs]
      ring

theorem isRdDecomposition_formula {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    IsRdDecomposition d p (rdDecompositionAFormula d p) (rdDecompositionBFormula d p) := by
  refine ⟨rdDecompositionFormula_eq_add_X_mul d p, natDegree_rdDecompositionAFormula_le hd,
    natDegree_rdDecompositionBFormula_le hd, rdDecompositionAFormula_fixed hd,
    rdDecompositionBFormula_fixed hd⟩

/-- Brändén--Solus Lemma 2.2: every polynomial of degree at most `d` has a
unique symmetric `R_d`-decomposition, again matching the explicit formulas. -/
theorem rdDecompositionExistsUnique {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d) :
    ∃! ab : ℝ[X] × ℝ[X],
      IsRdDecomposition d p ab.1 ab.2 ∧
      ab.1 = rdDecompositionAFormula d p ∧
      ab.2 = rdDecompositionBFormula d p := by
  refine ⟨⟨rdDecompositionAFormula d p, rdDecompositionBFormula d p⟩, ?_, ?_⟩
  · exact ⟨isRdDecomposition_formula hd, rfl, rfl⟩
  · lia

lemma eq_zero_of_natDegree_le_zero_of_eq_add_X_mul {p a b : ℝ[X]}
    (hp : p.natDegree ≤ 0) (ha : a.natDegree ≤ 0) (hb : b.natDegree ≤ 0) (h : p = a + X * b) :
    b = 0 := by
  have hp1 : p.coeff 1 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by lia))
  have ha1 : a.coeff 1 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ha (by lia))
  rw [h, Polynomial.coeff_add, Polynomial.coeff_X_mul, ha1, zero_add] at hp1
  have hbC : b = C (b.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hb
  grind

theorem idTransform_eq_add_of_isIdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d) (h : IsIdDecomposition d p a b) :
    idTransform d p = a + b := by
  rcases h with ⟨hab, had, hbd, hfixA, hfixB⟩
  cases d with
  | zero =>
      have hb0 : b = 0 := eq_zero_of_natDegree_le_zero_of_eq_add_X_mul hd had hbd hab
      simp_all
  | succ n =>
      have hfixB' : idTransform n b = b := by lia
      have hXb : idTransform (n + 1) (X * b) = b := by
        simpa [Nat.succ_sub_one] using (idTransform_X_mul_succ (d := n) (p := b) hbd).trans hfixB'
      simp_all

theorem idDecomposition_eq_formula_of_isIdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d) (h : IsIdDecomposition d p a b) :
    a = idDecompositionAFormula d p ∧ b = idDecompositionBFormula d p :=
  idDecompositionFormula_eq_of_system hd h.1 <|
    idTransform_eq_add_of_isIdDecomposition hd h

theorem rdTransform_eq_add_X_add_one_mul_of_isRdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hp : p.natDegree ≤ d) (h : IsRdDecomposition d p a b) :
    rdTransform d p = a + (X + 1) * b := by
  rcases h with ⟨hab, had, hbd, hfixA, hfixB⟩
  cases d with
  | zero =>
      have hb0 : b = 0 := eq_zero_of_natDegree_le_zero_of_eq_add_X_mul hp had hbd hab
      simp_all
  | succ n =>
      have hfixB' : rdTransform n b = b := by lia
      rw [hab, rdTransform_add, hfixA, rdTransform_X_mul_succ, hfixB']

theorem rdDecomposition_eq_formula_of_isRdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hp : p.natDegree ≤ d) (h : IsRdDecomposition d p a b) :
    a = rdDecompositionAFormula d p ∧ b = rdDecompositionBFormula d p :=
  rdDecompositionFormula_eq_of_system h.1 <|
    rdTransform_eq_add_X_add_one_mul_of_isRdDecomposition hp h

theorem isRdDecomposition_fPolynomial_of_isIdDecomposition {d : ℕ} {h a b : ℝ[X]}
    (hd : h.natDegree ≤ d) (hid : IsIdDecomposition d h a b) :
    IsRdDecomposition d (fPolynomial d h) (fPolynomial d a) (fPolynomial (d - 1) b) := by
  rcases hid with ⟨hab, had, hbd, hfixA, hfixB⟩
  refine ⟨?_, fPolynomial_natDegree_le d a, fPolynomial_natDegree_le (d - 1) b, ?_, ?_⟩
  · cases d with
    | zero =>
        have hb0 : b = 0 := eq_zero_of_natDegree_le_zero_of_eq_add_X_mul hd had hbd hab
        simp_all
    | succ n =>
        rw [hab, fPolynomial_add]
        rw [show fPolynomial (n + 1) (X * b) = X * fPolynomial (n + 1 - 1) b by
          simpa [Nat.succ_sub_one] using (fPolynomial_X_mul_succ n b)]
  · rw [rdTransform_fPolynomial, hfixA]
  · rw [rdTransform_fPolynomial, hfixB]

/-- Brändén--Solus Lemma 2.3, relating the `I_d`- and `R_d`-decompositions
through the `f`-polynomial transform. -/
theorem fPolynomialDecompositionCompatibility {d : ℕ} {h a b aTilde bTilde : ℝ[X]}
    (hd : h.natDegree ≤ d) (hid : IsIdDecomposition d h a b)
    (hrd : IsRdDecomposition d (fPolynomial d h) aTilde bTilde) :
    aTilde = fPolynomial d a ∧
    bTilde = fPolynomial (d - 1) b := by
  have hleft := rdDecomposition_eq_formula_of_isRdDecomposition
    (p := fPolynomial d h) (a := aTilde) (b := bTilde) (fPolynomial_natDegree_le d h) hrd
  have hright := rdDecomposition_eq_formula_of_isRdDecomposition
    (p := fPolynomial d h) (a := fPolynomial d a) (b := fPolynomial (d - 1) b)
    (fPolynomial_natDegree_le d h) (isRdDecomposition_fPolynomial_of_isIdDecomposition hd hid)
  lia

@[deprecated (since := "2026-10-05")]
alias IdTransform_natDegree_le := idTransform_natDegree_le

@[deprecated (since := "2026-10-05")]
alias IdTransform_X_mul_succ := idTransform_X_mul_succ

@[deprecated (since := "2026-10-05")]
alias IdTransform_of_natDegree_le_pred := idTransform_of_natDegree_le_pred

@[deprecated (since := "2026-10-05")]
alias IdTransform_X_mul_of_natDegree_le_pred := idTransform_X_mul_of_natDegree_le_pred

end RealRooted
