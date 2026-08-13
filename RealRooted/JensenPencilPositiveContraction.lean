import RealRooted.FiniteFreeRootCount
import RealRooted.CoefficientShape

/-!
# Positive Jensen-pencil contraction

This file proves the Schur--Szegő compatibility contraction when the three
PF inputs have positive constant coefficient.  Signed reciprocal reversal
reduces the statement to two finite-free upper-root-count contractions.
-/

open Polynomial
noncomputable section
namespace RealRooted

theorem coeff_one_pos_of_isPFPolynomial_of_coeff_zero_pos_of_natDegree_ne_zero
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hp0 : 0 < p.coeff 0)
    (hdeg : p.natDegree ≠ 0) : 0 < p.coeff 1 := by
  have hpne : p ≠ 0 := by
    intro h
    subst p
    simp at hp0
  have htop : 0 < p.coeff p.natDegree := by
    rw [← Polynomial.leadingCoeff]
    exact hp.hasNonnegCoeffs.pos_leadingCoeff hpne
  have hone_ne : p.coeff 1 ≠ 0 := by
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hdeg) with hdegree | hdegree
    · simpa [hdegree] using htop.ne'
    · exact
        (hasNoInternalCoeffZeros_of_hasNonnegCoeffs_of_eq_zero_or_splits
          hp.1 hp.2.1) 0 1 p.natDegree (by lia) hdegree le_rfl
          hp0.ne' htop.ne'
  exact lt_of_le_of_ne (hp.hasNonnegCoeffs 1) (Ne.symm hone_ne)

def monicSignedReciprocal (d : ℕ) (F : ℝ[X]) : ℝ[X] :=
  C (F.coeff 0)⁻¹ * signedReciprocal d F

theorem monic_monicSignedReciprocal {d : ℕ} {F : ℝ[X]}
    (hFdeg : F.natDegree ≤ d) (hF0 : F.coeff 0 ≠ 0) :
    (monicSignedReciprocal d F).Monic := by
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [leadingCoeff_signedReciprocal_eq_coeff_zero hFdeg hF0]
  exact inv_mul_cancel₀ hF0

theorem natDegree_monicSignedReciprocal {d : ℕ} {F : ℝ[X]}
    (hFdeg : F.natDegree ≤ d) (hF0 : F.coeff 0 ≠ 0) :
    (monicSignedReciprocal d F).natDegree = d := by
  rw [monicSignedReciprocal, natDegree_C_mul (inv_ne_zero hF0)]
  exact natDegree_signedReciprocal_eq_of_coeff_zero_ne hFdeg hF0

theorem splits_monicSignedReciprocal {d : ℕ} {F : ℝ[X]}
    (hFdeg : F.natDegree ≤ d) (hFs : F.Splits) :
    (monicSignedReciprocal d F).Splits := by
  exact (signedReciprocal_splits_of_splits hFdeg hFs).C_mul _

theorem roots_monicSignedReciprocal {d : ℕ} {F : ℝ[X]}
    (hF0 : F.coeff 0 ≠ 0) :
    (monicSignedReciprocal d F).roots = (signedReciprocal d F).roots := by
  rw [monicSignedReciprocal, Polynomial.roots_C_mul _ (inv_ne_zero hF0)]

theorem roots_signedReciprocal_nonneg {d : ℕ} {F : ℝ[X]}
    (hF : IsPFPolynomial F) (hFdeg : F.natDegree ≤ d)
    (hF0 : F.coeff 0 ≠ 0) :
    ∀ r ∈ (signedReciprocal d F).roots, 0 ≤ r := by
  have hFne : F ≠ 0 := by
    intro h
    subst F
    simp at hF0
  have hFs : F.Splits := hF.2.1.resolve_left hFne
  let q := F.comp (-X)
  have hqdeg : q.natDegree ≤ d := by
    dsimp [q]
    rw [Polynomial.natDegree_comp]
    simpa using hFdeg
  have hq0 : q.coeff 0 ≠ 0 := by
    simpa [q, Polynomial.coeff_zero_eq_eval_zero] using hF0
  have hqsplit : q.Splits := hFs.comp_neg_X
  have hrev0 : q.reverse ≠ 0 :=
    DegreeDropReversal.reverse_ne_zero_of_coeff_zero_ne hq0
  intro r hr
  rw [signedReciprocal,
    DegreeDropReversal.reflect_eq_X_pow_mul_reverse q hqdeg,
    Polynomial.roots_mul
      (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hrev0),
    Polynomial.roots_pow, Polynomial.roots_X, Multiset.mem_add] at hr
  rcases hr with hr | hr
  · rw [Multiset.mem_nsmul, Multiset.mem_singleton] at hr
    rcases hr with ⟨_, rfl⟩
    exact le_rfl
  · obtain ⟨y, hy, rfl⟩ :=
      (DegreeDropReversal.mem_roots_reverse_iff hqsplit hq0).mp hr
    dsimp [q] at hy
    rw [Polynomial.roots_comp_neg_X] at hy
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
    exact inv_nonneg.mpr (neg_nonneg.mpr (hF.roots_nonpos x hx))

theorem card_roots_monicSignedReciprocal_filter_ge_of_nonpos
    {d : ℕ} {F : ℝ[X]} (hF : IsPFPolynomial F)
    (hFdeg : F.natDegree ≤ d) (hF0 : F.coeff 0 ≠ 0)
    {s : ℝ} (hs : s ≤ 0) :
    ((monicSignedReciprocal d F).roots.filter (s ≤ ·)).card = d := by
  rw [roots_monicSignedReciprocal hF0, Multiset.filter_eq_self.mpr]
  · rw [card_roots_of_splits
      (signedReciprocal_splits_of_splits hFdeg
        (hF.2.1.resolve_left (by
          intro h
          subst F
          simp at hF0))),
      natDegree_signedReciprocal_eq_of_coeff_zero_ne hFdeg hF0]
  · intro r hr
    exact hs.trans (roots_signedReciprocal_nonneg hF hFdeg hF0 r hr)

theorem monicSignedReciprocal_rootCount_band
    {d : ℕ} {A B : ℝ[X]}
    (hA : IsPFPolynomial A) (hB : IsPFPolynomial B)
    (hAdeg : A.natDegree ≤ d) (hBdeg : B.natDegree ≤ d)
    (hA0 : 0 < A.coeff 0) (hB0 : 0 < B.coeff 0)
    (hcount : LiuOppositeSigns.RootCountCompatible A (X * B)) :
    ∀ s : ℝ,
      ((monicSignedReciprocal d B).roots.filter (s ≤ ·)).card ≤
        ((monicSignedReciprocal d A).roots.filter (s ≤ ·)).card ∧
      ((monicSignedReciprocal d A).roots.filter (s ≤ ·)).card ≤
        ((monicSignedReciprocal d B).roots.filter (s ≤ ·)).card + min 2 d := by
  have hBne : B ≠ 0 := by
    intro h
    subst B
    simp at hB0
  intro s
  by_cases hs : 0 < s
  · rw [roots_monicSignedReciprocal hB0.ne',
      roots_monicSignedReciprocal hA0.ne',
      card_roots_signedReciprocal_filter_ge hB hBdeg hB0.ne' hs,
      card_roots_signedReciprocal_filter_ge hA hAdeg hA0.ne' hs]
    have hc := hcount (-s⁻¹)
    rw [LiuOppositeSigns.rootCountAtOrAbove_X_mul hBne (-s⁻¹),
      if_pos (neg_nonpos.mpr (inv_nonneg.mpr hs.le))] at hc
    unfold LiuOppositeSigns.rootCountAtOrAbove at hc
    rw [abs_le] at hc
    constructor
    · lia
    · by_cases hd2 : 2 ≤ d
      · rw [min_eq_left hd2]
        lia
      · have hPAcard :
            (A.roots.filter (-s⁻¹ ≤ ·)).card ≤ d := by
          exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans (by
            rw [card_roots_of_splits
              (hA.2.1.resolve_left (by
                intro h
                subst A
                simp at hA0))]
            exact hAdeg)
        have hdmin : d = min 2 d := by rw [min_eq_right (Nat.le_of_not_ge hd2)]
        rw [← hdmin]
        lia
  · have hs0 : s ≤ 0 := le_of_not_gt hs
    rw [card_roots_monicSignedReciprocal_filter_ge_of_nonpos
        hA hAdeg hA0.ne' hs0,
      card_roots_monicSignedReciprocal_filter_ge_of_nonpos
        hB hBdeg hB0.ne' hs0]
    simp

theorem schurSzegoComp_monicSignedReciprocal_reflect
    (d : ℕ) (F p : ℝ[X]) :
    schurSzegoComp d (monicSignedReciprocal d F) (reflect d p) =
      C (F.coeff 0)⁻¹ *
        signedReciprocal d (schurSzegoComp d F p) := by
  rw [monicSignedReciprocal, schurSzegoComp_C_mul_left,
    ← finiteFreeMultiplicativeConvolution_signedReciprocal_right,
    ← signedReciprocal_schurSzegoComp]

theorem signedReciprocal_schurSzegoComp_rootCount_band
    {d : ℕ} {A B p : ℝ[X]} (hd : d ≠ 0)
    (hA : IsPFPolynomial A) (hB : IsPFPolynomial B)
    (hp : IsPFPolynomial p)
    (hAdeg : A.natDegree ≤ d) (hBdeg : B.natDegree ≤ d)
    (hpdeg : p.natDegree ≤ d)
    (hA0 : 0 < A.coeff 0) (hB0 : 0 < B.coeff 0)
    (hp0 : p.coeff 0 ≠ 0) (hp1 : 0 < p.coeff 1)
    (hcompat : Compatible A (X * B)) :
    ∀ t : ℝ,
      ((signedReciprocal d (schurSzegoComp d B p)).roots.filter
          (t < ·)).card ≤
        ((signedReciprocal d (schurSzegoComp d A p)).roots.filter
          (t < ·)).card ∧
      ((signedReciprocal d (schurSzegoComp d A p)).roots.filter
          (t < ·)).card ≤
        ((signedReciprocal d (schurSzegoComp d B p)).roots.filter
          (t < ·)).card + min 2 d := by
  have hAne : A ≠ 0 := by
    intro h
    subst A
    simp at hA0
  have hBne : B ≠ 0 := by
    intro h
    subst B
    simp at hB0
  have hXB : IsPFPolynomial (X * B) := hB.X_mul
  have hXBne : X * B ≠ 0 := mul_ne_zero X_ne_zero hBne
  have hcount : LiuOppositeSigns.RootCountCompatible A (X * B) :=
    LiuOppositeSigns.RootCountCompatible.of_compatible hcompat
      (hA.hasNonnegCoeffs.pos_leadingCoeff hAne)
      (hXB.hasNonnegCoeffs.pos_leadingCoeff hXBne)
  have hband := monicSignedReciprocal_rootCount_band hA hB hAdeg hBdeg
    hA0 hB0 hcount
  have hBA := rootCountAbove_schurSzegoComp_reflect_le_add
    (d := d) (ell := 0) (P := monicSignedReciprocal d A)
    (Q := monicSignedReciprocal d B) (p := p) hd
    (monic_monicSignedReciprocal hAdeg hA0.ne')
    (monic_monicSignedReciprocal hBdeg hB0.ne')
    (splits_monicSignedReciprocal hAdeg
      (hA.eq_zero_or_splits.resolve_left hAne))
    (splits_monicSignedReciprocal hBdeg
      (hB.eq_zero_or_splits.resolve_left hBne))
    (natDegree_monicSignedReciprocal hAdeg hA0.ne')
    (natDegree_monicSignedReciprocal hBdeg hB0.ne')
    (Nat.zero_le d) hp hpdeg hp0 hp1 (fun x => by simpa using (hband x).1)
  have hAB := rootCountAbove_schurSzegoComp_reflect_le_add
    (d := d) (ell := min 2 d) (P := monicSignedReciprocal d B)
    (Q := monicSignedReciprocal d A) (p := p) hd
    (monic_monicSignedReciprocal hBdeg hB0.ne')
    (monic_monicSignedReciprocal hAdeg hA0.ne')
    (splits_monicSignedReciprocal hBdeg
      (hB.eq_zero_or_splits.resolve_left hBne))
    (splits_monicSignedReciprocal hAdeg
      (hA.eq_zero_or_splits.resolve_left hAne))
    (natDegree_monicSignedReciprocal hBdeg hB0.ne')
    (natDegree_monicSignedReciprocal hAdeg hA0.ne')
    (min_le_right 2 d) hp hpdeg hp0 hp1 (fun x => (hband x).2)
  intro t
  constructor
  · have ht := hBA t
    rw [schurSzegoComp_monicSignedReciprocal_reflect,
      schurSzegoComp_monicSignedReciprocal_reflect,
      Polynomial.roots_C_mul _ (inv_ne_zero hB0.ne'),
      Polynomial.roots_C_mul _ (inv_ne_zero hA0.ne')] at ht
    simpa using ht
  · have ht := hAB t
    rw [schurSzegoComp_monicSignedReciprocal_reflect,
      schurSzegoComp_monicSignedReciprocal_reflect,
      Polynomial.roots_C_mul _ (inv_ne_zero hA0.ne'),
      Polynomial.roots_C_mul _ (inv_ne_zero hB0.ne')] at ht
    exact ht

theorem card_roots_signedReciprocal_filter_gt
    {d : ℕ} {F : ℝ[X]} (hF : IsPFPolynomial F)
    (hFdeg : F.natDegree ≤ d) (hF0 : F.coeff 0 ≠ 0)
    {s : ℝ} (hs : 0 < s) :
    ((signedReciprocal d F).roots.filter (s < ·)).card =
      (F.roots.filter (-s⁻¹ < ·)).card := by
  have hFne : F ≠ 0 := by
    intro hzero
    subst F
    simp at hF0
  have hFsplit : F.Splits := hF.2.1.resolve_left hFne
  let q := F.comp (-X)
  have hqsplit : q.Splits := hFsplit.comp_neg_X
  have hq0 : q.coeff 0 ≠ 0 := by
    simpa [q, Polynomial.coeff_zero_eq_eval_zero] using hF0
  have hqdeg : q.natDegree ≤ d := by
    dsimp [q]
    rw [Polynomial.natDegree_comp]
    simpa using hFdeg
  have hrev0 : q.reverse ≠ 0 :=
    DegreeDropReversal.reverse_ne_zero_of_coeff_zero_ne hq0
  have hpad :
      Multiset.filter (s < ·)
        ((d - q.natDegree) • ({0} : Multiset ℝ)) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x hx
    rw [Multiset.mem_nsmul, Multiset.mem_singleton] at hx
    rcases hx with ⟨_, rfl⟩
    exact (not_lt_of_ge hs.le)
  rw [signedReciprocal,
    DegreeDropReversal.reflect_eq_X_pow_mul_reverse q hqdeg,
    Polynomial.roots_mul
      (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hrev0),
    Polynomial.roots_pow, Polynomial.roots_X, Multiset.filter_add,
    Multiset.card_add, hpad, Multiset.card_zero, zero_add,
    DegreeDropReversal.card_filter_reverse_roots hqsplit hq0]
  dsimp [q]
  rw [Polynomial.roots_comp_neg_X, Multiset.filter_map, Multiset.card_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro x hx
  have hxle : x ≤ 0 := hF.2.2 x hx
  have hxne : x ≠ 0 := by
    intro hxzero
    subst x
    have hroot : F.IsRoot 0 := (Polynomial.mem_roots hFne).mp hx
    exact hF0 (by
      simpa [Polynomial.IsRoot.def, Polynomial.coeff_zero_eq_eval_zero]
        using hroot)
  have hxneg : x < 0 := lt_of_le_of_ne hxle hxne
  have hnegpos : 0 < -x := neg_pos.mpr hxneg
  change (s < (-x)⁻¹) ↔ -s⁻¹ < x
  rw [lt_inv_comm₀ hs hnegpos]
  constructor <;> intro h <;> linarith

theorem compatible_schurSzego_jensen_of_positive_constants_of_nonconstant
    {d : ℕ} {A B p : ℝ[X]}
    (hA : IsPFPolynomial A) (hB : IsPFPolynomial B)
    (hp : IsPFPolynomial p)
    (hAdeg : A.natDegree ≤ d) (hBdeg : B.natDegree ≤ d)
    (hpdeg : p.natDegree ≤ d)
    (hA0 : 0 < A.coeff 0) (hB0 : 0 < B.coeff 0)
    (hp0 : 0 < p.coeff 0) (hpdeg0 : p.natDegree ≠ 0)
    (hcompat : Compatible A (X * B)) :
    Compatible (schurSzegoComp d A p)
      (X * schurSzegoComp d B p) := by
  let U := schurSzegoComp d A p
  let V := schurSzegoComp d B p
  have hd : d ≠ 0 := by
    intro hd0
    subst d
    exact hpdeg0 (Nat.eq_zero_of_le_zero hpdeg)
  have hp1 : 0 < p.coeff 1 :=
    coeff_one_pos_of_isPFPolynomial_of_coeff_zero_pos_of_natDegree_ne_zero
      hp hp0 hpdeg0
  have hU : IsPFPolynomial U := hA.schurSzegoComp hp hAdeg hpdeg
  have hV : IsPFPolynomial V := hB.schurSzegoComp hp hBdeg hpdeg
  have hXV : IsPFPolynomial (X * V) := hV.X_mul
  have hU0 : 0 < U.coeff 0 := by
    dsimp [U]
    rw [coeff_schurSzegoComp_of_le (Nat.zero_le d)]
    simpa using mul_pos hA0 hp0
  have hV0 : 0 < V.coeff 0 := by
    dsimp [V]
    rw [coeff_schurSzegoComp_of_le (Nat.zero_le d)]
    simpa using mul_pos hB0 hp0
  have hUne : U ≠ 0 := by
    intro h
    exact hU0.ne' (by rw [h]; simp)
  have hVne : V ≠ 0 := by
    intro h
    exact hV0.ne' (by rw [h]; simp)
  have hXVne : X * V ≠ 0 := mul_ne_zero X_ne_zero hVne
  have hrec := signedReciprocal_schurSzegoComp_rootCount_band hd hA hB hp
    hAdeg hBdeg hpdeg hA0 hB0 hp0.ne' hp1 hcompat
  have hcount : LiuOppositeSigns.RootCountCompatible U (X * V) := by
    apply LiuOppositeSigns.RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot
      hUne hXVne
    intro x _hxU hxXV
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · have hxne : x ≠ 0 := ne_of_lt hx
      have hs : 0 < -x⁻¹ := neg_pos.mpr (inv_lt_zero.mpr hx)
      have hr := hrec (-x⁻¹)
      rw [card_roots_signedReciprocal_filter_gt hV
          (natDegree_schurSzegoComp_le d B p) hV0.ne' hs,
        card_roots_signedReciprocal_filter_gt hU
          (natDegree_schurSzegoComp_le d A p) hU0.ne' hs] at hr
      have hthreshold : -(-x⁻¹)⁻¹ = x := by
        simp
      rw [hthreshold] at hr
      have hXVcount :
          ((X * V).roots.filter (x < ·)).card =
            (V.roots.filter (x < ·)).card + 1 := by
        rw [Polynomial.roots_mul hXVne, Polynomial.roots_X,
          Multiset.filter_add, Multiset.card_add,
          Multiset.filter_singleton]
        simp [hx, Nat.add_comm]
      rw [hXVcount]
      have hmin : min 2 d ≤ 2 := min_le_left 2 d
      constructor <;> lia
    · exfalso
      apply hxXV
      simp [Polynomial.IsRoot.def]
    · have hUcount : (U.roots.filter (x < ·)).card = 0 := by
        rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
        intro r hr
        exact not_lt_of_ge ((hU.roots_nonpos r hr).trans hx.le)
      have hXVcount : ((X * V).roots.filter (x < ·)).card = 0 := by
        rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
        intro r hr
        exact not_lt_of_ge ((hXV.roots_nonpos r hr).trans hx.le)
      simp [hUcount, hXVcount]
  exact hcount.compatible_of_pf hU hXV hUne hXVne

theorem compatible_schurSzego_jensen_of_positive_constants
    {d : ℕ} {A B p : ℝ[X]}
    (hA : IsPFPolynomial A) (hB : IsPFPolynomial B)
    (hp : IsPFPolynomial p)
    (hAdeg : A.natDegree ≤ d) (hBdeg : B.natDegree ≤ d)
    (hpdeg : p.natDegree ≤ d)
    (hA0 : 0 < A.coeff 0) (hB0 : 0 < B.coeff 0)
    (hp0 : 0 < p.coeff 0)
    (hcompat : Compatible A (X * B)) :
    Compatible (schurSzegoComp d A p)
      (X * schurSzegoComp d B p) := by
  by_cases hpdeg0 : p.natDegree = 0
  · let U := schurSzegoComp d A p
    let V := schurSzegoComp d B p
    have hU : IsPFPolynomial U := hA.schurSzegoComp hp hAdeg hpdeg
    have hV : IsPFPolynomial V := hB.schurSzegoComp hp hBdeg hpdeg
    have hXV : IsPFPolynomial (X * V) := hV.X_mul
    have hU0 : 0 < U.coeff 0 := by
      dsimp [U]
      rw [coeff_schurSzegoComp_of_le (Nat.zero_le d)]
      simpa using mul_pos hA0 hp0
    have hV0 : 0 < V.coeff 0 := by
      dsimp [V]
      rw [coeff_schurSzegoComp_of_le (Nat.zero_le d)]
      simpa using mul_pos hB0 hp0
    have hUne : U ≠ 0 := by
      intro h
      exact hU0.ne' (by rw [h]; simp)
    have hVne : V ≠ 0 := by
      intro h
      exact hV0.ne' (by rw [h]; simp)
    have hXVne : X * V ≠ 0 := mul_ne_zero X_ne_zero hVne
    have hUdeg : U.natDegree = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact (natDegree_schurSzegoComp_le_right d A p).trans hpdeg0.le
    have hVdeg : V.natDegree = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact (natDegree_schurSzegoComp_le_right d B p).trans hpdeg0.le
    have hXVdeg : (X * V).natDegree ≤ 1 := by
      rw [Polynomial.natDegree_X_mul hVne, hVdeg]
    have hcount :=
      LiuOppositeSigns.RootCountCompatible.of_left_natDegree_zero_right_natDegree_le_one
        (hU.eq_zero_or_splits.resolve_left hUne)
        (hXV.eq_zero_or_splits.resolve_left hXVne) hUdeg hXVdeg
    exact hcount.compatible_of_pf hU hXV hUne hXVne
  · exact compatible_schurSzego_jensen_of_positive_constants_of_nonconstant
      hA hB hp hAdeg hBdeg hpdeg hA0 hB0 hp0 hpdeg0 hcompat

end RealRooted
