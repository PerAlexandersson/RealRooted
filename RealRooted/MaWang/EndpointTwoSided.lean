module

public import RealRooted.MaWang.EndpointMultiplicity
import RealRooted.DerivativeRecurrence.EndpointWindow
import RealRooted.Linear
import RealRooted.MaWang.DerivativeStep
import RealRooted.WagnerRightSum.Sign

/-!
# Closed endpoint derivative steps

We prove the two-endpoint criterion for
`(a X + c) f + X (X + 1) f'`, including roots and multiplicities at both
closed endpoints.  The proof factors the full zero multiplicity before using
the half-open endpoint criterion of Ma and Wang.
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

private lemma endpointStep_zero_factorization (a c : ℝ) (p q : ℝ[X]) (m : ℕ)
    (hpq : X ^ m * q = p) :
    MaWang.endpointStep 1 a c p = X ^ m *
      MaWang.endpointStep 1 (a + m) (c + m) q := by
  rw [MaWang.endpointStep, ← hpq]
  cases m with
  | zero => simp [MaWang.endpointStep]
  | succ m =>
      rw [derivative_mul, derivative_X_pow]
      simp only [Nat.cast_succ]
      rw [MaWang.endpointStep]
      rw [Nat.add_sub_cancel_right]
      simp only [map_one, map_add, map_natCast]
      ring

private lemma roots_zero_cofactor_mem_Ico {p q : ℝ[X]} {m : ℕ}
    (hq : q ≠ 0) (hfactor : X ^ m * q = p) (hqeval : q.eval 0 ≠ 0)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) :
    ∀ r ∈ q.roots, -1 ≤ r ∧ r < 0 := by
  intro r hr
  have hrq : q.IsRoot r := (mem_roots hq).mp hr
  have hrp : r ∈ p.roots := by
    rw [← hfactor, roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hq),
      Multiset.mem_add]
    exact Or.inr hr
  exact ⟨(hroots r hrp).1, lt_of_le_of_ne (hroots r hrp).2 fun hre =>
    hqeval (by simpa [hre] using hrq)⟩

private lemma zero_cofactor_rootMultiplicity_neg_one {p q : ℝ[X]} {m : ℕ}
    (hq : q ≠ 0) (hfactor : X ^ m * q = p) :
    q.rootMultiplicity (-1) = p.rootMultiplicity (-1) := by
  have hprod : X ^ m * q ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hq
  rw [← hfactor, rootMultiplicity_mul hprod]
  have hnotroot : ¬(X ^ m : ℝ[X]).IsRoot (-1) := by
    simp [Polynomial.IsRoot.def]
  rw [rootMultiplicity_eq_zero hnotroot, zero_add]

/-- A positive affine coefficient gives a successor-degree interlacing step
even when the input has roots at either endpoint of `[-1, 0]`. -/
theorem affineEndpointStep_strictInterl {a c : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) :
    (MaWang.endpointStep 1 a c p).natDegree = p.natDegree + 1 ∧
      HasPosLeadingCoeff (MaWang.endpointStep 1 a c p) ∧
      StrictInterl p (MaWang.endpointStep 1 a c p) := by
  have hpack := MaWang.endpointStep_natDegree_eq_and_leadingCoeff_pos
    (c := 1) (b := c) ha hp
  refine ⟨hpack.1, hpack.2, ?_⟩
  have hroot_lo : ∀ r, p.IsRoot r → -1 ≤ r := by
    intro r hr
    exact (hroots r ((mem_roots hp.ne_zero).mpr hr)).1
  have hroot_hi : ∀ r, p.IsRoot r → r ≤ 0 := by
    intro r hr
    exact (hroots r ((mem_roots hp.ne_zero).mpr hr)).2
  have hform :
      (C a * X + C c) * p + (X * (1 + X)) * p.derivative =
        MaWang.endpointStep 1 a c p := by
    rw [MaWang.endpointStep]
    simp only [map_one]
    ring
  have hinter := MaWang.strictInterl_derivative_X_mul_one_add_X_of_roots_in_Icc_of_splits
    (f := p) (u := C a * X + C c) hs
    (by rw [hform, hpack.1]; lia)
    (by rw [hform, hpack.1])
    (by rw [hform]; exact hpack.2) hp hroot_lo hroot_hi
  rw [hform] at hinter
  exact hinter

/-- At zero, the endpoint step preserves multiplicity unless the affine
threshold vanishes, in which case the multiplicity increases by one. -/
theorem affineEndpointStep_rootMultiplicity_zero {a c : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) :
    (MaWang.endpointStep 1 a c p).rootMultiplicity 0 =
      if c + p.rootMultiplicity 0 = 0 then p.rootMultiplicity 0 + 1
      else p.rootMultiplicity 0 := by
  let m := p.rootMultiplicity 0
  let q := p /ₘ X ^ m
  let H := MaWang.endpointStep 1 (a + m) (c + m) q
  have hfactor : X ^ m * q = p := by
    dsimp [q, m]
    simpa using p.pow_mul_divByMonic_rootMultiplicity_eq 0
  have hqeval : q.eval 0 ≠ 0 := by
    dsimp [q, m]
    simpa using eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hp.ne_zero
  have hq : q ≠ 0 := fun hqzero => hqeval (by rw [hqzero, eval_zero])
  have hqpos : HasPosLeadingCoeff q := by
    apply hasPosLeadingCoeff_of_pow_X_sub_C_mul (r := 0) (m := m)
    simpa using (show HasPosLeadingCoeff (X ^ m * q) by rw [hfactor]; exact hp)
  have hqs : q.Splits :=
    (isRealRooted_of_dvd hp.ne_zero hs hq
      ⟨X ^ m, by rw [mul_comm, hfactor]⟩).2
  have hqroots : ∀ r ∈ q.roots, -1 ≤ r ∧ r < 0 :=
    roots_zero_cofactor_mem_Ico hq hfactor hqeval hroots
  have ha' : 0 < a + (m : ℝ) := by positivity
  have hHpack := MaWang.endpointStep_natDegree_eq_and_leadingCoeff_pos
    (c := 1) (b := c + m) ha' hqpos
  have hinter := MaWang.endpointStep_strictInterl
    (c := 1) (b := c + m) ha' hqpos hqs hqroots
  have hFfactor : MaWang.endpointStep 1 a c p = X ^ m * H := by
    dsimp [H]
    exact endpointStep_zero_factorization a c p q m hfactor
  have hHne : H ≠ 0 := hHpack.2.ne_zero
  have hmult : (MaWang.endpointStep 1 a c p).rootMultiplicity 0 =
      m + H.rootMultiplicity 0 := by
    rw [hFfactor, rootMultiplicity_mul
      (mul_ne_zero (pow_ne_zero _ X_ne_zero) hHne)]
    simpa using (Polynomial.rootMultiplicity_X_sub_C_pow (R := ℝ) 0 m)
  have hqmult : q.rootMultiplicity 0 = 0 := by
    apply rootMultiplicity_eq_zero
    simpa [Polynomial.IsRoot.def] using hqeval
  have hHmult : H.rootMultiplicity 0 = if c + (m : ℝ) = 0 then 1 else 0 := by
    split_ifs with heq
    · have hroot : H.IsRoot 0 := by
        rw [Polynomial.IsRoot.def]
        simp [H, heq]
      have hpos : 0 < H.rootMultiplicity 0 := (rootMultiplicity_pos hHne).2 hroot
      have hle := (hinter.rootMultiplicity_bounds 0).2
      rw [hqmult] at hle
      lia
    · apply rootMultiplicity_eq_zero
      rw [Polynomial.IsRoot.def]
      rw [show H.eval 0 = (c + (m : ℝ)) * q.eval 0 by
        exact MaWang.endpointStep_eval_zero 1 (a + m) (c + m) q]
      exact mul_ne_zero heq hqeval
  dsimp [m] at hmult hHmult ⊢
  rw [hmult, hHmult]
  split_ifs <;> rfl

/-- At `-1`, the endpoint step preserves multiplicity unless the affine
threshold is an equality, in which case the multiplicity increases by one. -/
theorem affineEndpointStep_rootMultiplicity_neg_one {a c : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) :
    (MaWang.endpointStep 1 a c p).rootMultiplicity (-1) =
      if c = a + p.rootMultiplicity (-1) then p.rootMultiplicity (-1) + 1
      else p.rootMultiplicity (-1) := by
  let m := p.rootMultiplicity 0
  let q := p /ₘ X ^ m
  let H := MaWang.endpointStep 1 (a + m) (c + m) q
  have hfactor : X ^ m * q = p := by
    dsimp [q, m]
    simpa using p.pow_mul_divByMonic_rootMultiplicity_eq 0
  have hqeval : q.eval 0 ≠ 0 := by
    dsimp [q, m]
    simpa using eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hp.ne_zero
  have hq : q ≠ 0 := fun hqzero => hqeval (by rw [hqzero, eval_zero])
  have hqpos : HasPosLeadingCoeff q := by
    apply hasPosLeadingCoeff_of_pow_X_sub_C_mul (r := 0) (m := m)
    simpa using (show HasPosLeadingCoeff (X ^ m * q) by rw [hfactor]; exact hp)
  have hqs : q.Splits :=
    (isRealRooted_of_dvd hp.ne_zero hs hq
      ⟨X ^ m, by rw [mul_comm, hfactor]⟩).2
  have hqroots : ∀ r ∈ q.roots, -1 ≤ r ∧ r < 0 :=
    roots_zero_cofactor_mem_Ico hq hfactor hqeval hroots
  have ha' : 0 < a + (m : ℝ) := by positivity
  have hHpack := MaWang.endpointStep_natDegree_eq_and_leadingCoeff_pos
    (c := 1) (b := c + m) ha' hqpos
  have hFfactor : MaWang.endpointStep 1 a c p = X ^ m * H := by
    dsimp [H]
    exact endpointStep_zero_factorization a c p q m hfactor
  have hHne : H ≠ 0 := hHpack.2.ne_zero
  have hFmult : (MaWang.endpointStep 1 a c p).rootMultiplicity (-1) =
      H.rootMultiplicity (-1) := by
    rw [hFfactor, rootMultiplicity_mul
      (mul_ne_zero (pow_ne_zero _ X_ne_zero) hHne)]
    have hnotroot : ¬(X ^ m : ℝ[X]).IsRoot (-1) := by
      simp [Polynomial.IsRoot.def]
    rw [rootMultiplicity_eq_zero hnotroot, zero_add]
  have hqmult := zero_cofactor_rootMultiplicity_neg_one hq hfactor
  have hHmult := MaWang.endpointStep_rootMultiplicity
    (c := 1) (a := a + m) (b := c + m) ha' hqpos hqs hqroots
  change H.rootMultiplicity (-1) = _ at hHmult
  rw [hqmult] at hHmult
  rw [hFmult, hHmult]
  by_cases heq : c = a + (p.rootMultiplicity (-1) : ℝ)
  · rw [ite_eq_left heq]
    rw [ite_eq_left (by rw [heq]; ring)]
  · rw [ite_eq_right heq]
    rw [ite_eq_right (fun h => heq (by nlinarith))]

/-- The Ma--Wang affine derivative step has all roots in `[-1, 0]` exactly
when its two endpoint thresholds are nonnegative. -/
theorem affineEndpointStep_roots_mem_Icc_iff {a c : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) :
    (∀ r ∈ (MaWang.endpointStep 1 a c p).roots, r ∈ Icc (-1 : ℝ) 0) ↔
      0 ≤ c + p.rootMultiplicity 0 ∧
        0 ≤ a + p.rootMultiplicity (-1) - c := by
  let m := p.rootMultiplicity 0
  let q := p /ₘ X ^ m
  let H := MaWang.endpointStep 1 (a + m) (c + m) q
  have hfactor : X ^ m * q = p := by
    dsimp [q, m]
    simpa using p.pow_mul_divByMonic_rootMultiplicity_eq 0
  have hqeval : q.eval 0 ≠ 0 := by
    dsimp [q, m]
    simpa using eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hp.ne_zero
  have hq : q ≠ 0 := fun hqzero => hqeval (by rw [hqzero, eval_zero])
  have hqpos : HasPosLeadingCoeff q := by
    apply hasPosLeadingCoeff_of_pow_X_sub_C_mul (r := 0) (m := m)
    simpa using (show HasPosLeadingCoeff (X ^ m * q) by rw [hfactor]; exact hp)
  have hqs : q.Splits :=
    (isRealRooted_of_dvd hp.ne_zero hs hq
      ⟨X ^ m, by rw [mul_comm, hfactor]⟩).2
  have hqroots : ∀ r ∈ q.roots, -1 ≤ r ∧ r < 0 :=
    roots_zero_cofactor_mem_Ico hq hfactor hqeval hroots
  have ha' : 0 < a + (m : ℝ) := by positivity
  have hHpack := MaWang.endpointStep_natDegree_eq_and_leadingCoeff_pos
    (c := 1) (b := c + m) ha' hqpos
  have hinterStrict := MaWang.endpointStep_strictInterl
    (c := 1) (b := c + m) ha' hqpos hqs hqroots
  have hinter : Interlaces q H := by
    apply hinterStrict.toInterlaces
    exact hHpack.1.symm
  have hFfactor : MaWang.endpointStep 1 a c p = X ^ m * H := by
    dsimp [H]
    exact endpointStep_zero_factorization a c p q m hfactor
  have hHne : H ≠ 0 := hHpack.2.ne_zero
  have hqmult := zero_cofactor_rootMultiplicity_neg_one hq hfactor
  have hlowerRaw := MaWang.endpointStep_roots_ge_neg_iff
    (c := 1) (a := a + m) (b := c + m) ha' hqpos hqs hqroots
  change (∀ r ∈ H.roots, -1 ≤ r) ↔ _ at hlowerRaw
  rw [hqmult] at hlowerRaw
  have hlower : (∀ r ∈ H.roots, -1 ≤ r) ↔
      0 ≤ a + p.rootMultiplicity (-1) - c := by
    rw [hlowerRaw]
    constructor <;> intro h <;> nlinarith
  have hqevalpos : 0 < q.eval 0 :=
    eval_pos_of_all_roots_lt hq hqs hqpos fun r hr => (hqroots r hr).2
  have hupperRaw := roots_le_iff_eval_nonneg_of_interlaces
    (U := 0) hinter hHpack.2 fun r hr => (hqroots r hr).2
  change (∀ r ∈ H.roots, r ≤ 0) ↔ _ at hupperRaw
  rw [show H.eval 0 = (c + (m : ℝ)) * q.eval 0 by
    exact MaWang.endpointStep_eval_zero 1 (a + m) (c + m) q] at hupperRaw
  have hupper : (∀ r ∈ H.roots, r ≤ 0) ↔ 0 ≤ c + (m : ℝ) := by
    rw [hupperRaw]
    constructor <;> intro h
    · nlinarith
    · exact mul_nonneg h hqevalpos.le
  have hprod : X ^ m * H ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hHne
  have htransfer :
      (∀ r ∈ (MaWang.endpointStep 1 a c p).roots, r ∈ Icc (-1 : ℝ) 0) ↔
        ∀ r ∈ H.roots, r ∈ Icc (-1 : ℝ) 0 := by
    constructor
    · intro hall r hr
      apply hall r
      rw [hFfactor, roots_mul hprod, Multiset.mem_add]
      exact Or.inr hr
    · intro hall r hr
      rw [hFfactor, roots_mul hprod, Multiset.mem_add] at hr
      rcases hr with hr | hr
      · have hre : r = 0 := by
          rw [show (X : ℝ[X]) = X - C 0 by simp] at hr
          have hm : m ≠ 0 ∧ r = 0 := by
            simpa only [roots_pow, roots_X_sub_C, Multiset.mem_nsmul,
              Multiset.mem_singleton] using hr
          exact hm.2
        subst r
        exact ⟨by norm_num, le_rfl⟩
      · exact hall r hr
  rw [htransfer]
  constructor
  · intro hall
    exact ⟨hupper.mp (fun r hr => (hall r hr).2),
      hlower.mp (fun r hr => (hall r hr).1)⟩
  · rintro ⟨hzero, hnegone⟩ r hr
    exact ⟨hlower.mpr hnegone r hr, hupper.mpr hzero r hr⟩

/-- The complete two-endpoint Ma--Wang step: degree, leading coefficient,
real-rootedness, directed weak interlacing, the closed-window criterion, and
both endpoint multiplicity updates. -/
theorem affineEndpointStep_closed {a c : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hp : HasPosLeadingCoeff p) (hs : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) :
    (MaWang.endpointStep 1 a c p).natDegree = p.natDegree + 1 ∧
      HasPosLeadingCoeff (MaWang.endpointStep 1 a c p) ∧
      (MaWang.endpointStep 1 a c p).Splits ∧
      Interlaces p (MaWang.endpointStep 1 a c p) ∧
      ((∀ r ∈ (MaWang.endpointStep 1 a c p).roots, r ∈ Icc (-1 : ℝ) 0) ↔
        0 ≤ c + p.rootMultiplicity 0 ∧
          0 ≤ a + p.rootMultiplicity (-1) - c) ∧
      ((MaWang.endpointStep 1 a c p).rootMultiplicity 0 =
        if c + p.rootMultiplicity 0 = 0 then p.rootMultiplicity 0 + 1
        else p.rootMultiplicity 0) ∧
      (MaWang.endpointStep 1 a c p).rootMultiplicity (-1) =
        if c = a + p.rootMultiplicity (-1) then p.rootMultiplicity (-1) + 1
        else p.rootMultiplicity (-1) := by
  have hstep := affineEndpointStep_strictInterl (c := c) ha hp hs hroots
  refine ⟨hstep.1, hstep.2.1, hstep.2.2.2.1.2,
    hstep.2.2.toInterlaces hstep.1.symm, ?_, ?_, ?_⟩
  · exact affineEndpointStep_roots_mem_Icc_iff (c := c) ha hp hs hroots
  · exact affineEndpointStep_rootMultiplicity_zero (c := c) ha hp hs hroots
  · exact affineEndpointStep_rootMultiplicity_neg_one (c := c) ha hp hs hroots

end RealRooted
