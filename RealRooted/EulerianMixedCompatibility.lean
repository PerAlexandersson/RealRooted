import RealRooted.ChudnovskySeymour
import RealRooted.GarloffWagner
import RealRooted.HermiteBiehler
import RealRooted.MaWang

/-!
# Adjacent Euler insertion operators

This file develops the two adjacent Euler operators used in compatibility
proofs for derangement descent polynomials.  The common parametrization

`E(c, d) p = (c + (d + 1) X) p + (X - X^2) p'`

contains the positive-boundary operator at `c = 1` and the zero-boundary
operator at `c = 0`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Euler insertion operator with constant boundary weight `c` and degree
bound `d`. -/
def eulerInsertionStep (c : ℝ) (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C c * p + C ((d : ℝ) + 1) * (X * p) +
    X * p.derivative - X * (X * p.derivative)

theorem eulerInsertionStep_eq (c : ℝ) (d : ℕ) (p : ℝ[X]) :
    eulerInsertionStep c d p =
      (C c + C ((d : ℝ) + 1) * X) * p +
        (X - X ^ 2) * p.derivative := by
  simp [eulerInsertionStep]
  ring

@[simp] theorem eulerInsertionStep_zero (c : ℝ) (d : ℕ) :
    eulerInsertionStep c d 0 = 0 := by
  simp [eulerInsertionStep]

@[simp] theorem coeff_eulerInsertionStep_zero (c : ℝ) (d : ℕ) (p : ℝ[X]) :
    (eulerInsertionStep c d p).coeff 0 = c * p.coeff 0 := by
  simp [eulerInsertionStep]

@[simp] theorem coeff_eulerInsertionStep_succ
    (c : ℝ) (d k : ℕ) (p : ℝ[X]) :
    (eulerInsertionStep c d p).coeff (k + 1) =
      (c + (k : ℝ) + 1) * p.coeff (k + 1) +
        ((d : ℝ) + 1 - k) * p.coeff k := by
  cases k with
  | zero =>
      simp only [eulerInsertionStep, coeff_sub, coeff_add, coeff_C_mul]
      simp [coeff_X_mul, coeff_derivative]
      ring
  | succ k =>
      simp only [eulerInsertionStep, coeff_sub, coeff_add, coeff_C_mul]
      simp [coeff_X_mul, coeff_derivative]
      ring

theorem eulerInsertionStep_add (c : ℝ) (d : ℕ) (p q : ℝ[X]) :
    eulerInsertionStep c d (p + q) =
      eulerInsertionStep c d p + eulerInsertionStep c d q := by
  simp [eulerInsertionStep, derivative_add]
  ring

theorem eulerInsertionStep_C_mul (c a : ℝ) (d : ℕ) (p : ℝ[X]) :
    eulerInsertionStep c d (C a * p) = C a * eulerInsertionStep c d p := by
  simp [eulerInsertionStep, derivative_mul]
  ring

theorem natDegree_eulerInsertionStep_le (c : ℝ) (d : ℕ) (p : ℝ[X]) :
    (eulerInsertionStep c d p).natDegree ≤ p.natDegree + 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  cases k with
  | zero => lia
  | succ k =>
      rw [coeff_eulerInsertionStep_succ]
      have hpk : p.coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (by lia)
      have hpks : p.coeff (k + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by lia)
      simp [hpk, hpks]

/-- Under the intended degree bound, an Euler insertion step raises degree by
one and retains a positive leading coefficient. -/
theorem eulerInsertionStep_degree_pos
    {c : ℝ} {d : ℕ} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hp_pos : HasPosLeadingCoeff p) :
    (eulerInsertionStep c d p).natDegree = p.natDegree + 1 ∧
      HasPosLeadingCoeff (eulerInsertionStep c d p) := by
  have hfactor : 0 < (d : ℝ) + 1 - p.natDegree := by
    have hcast : (p.natDegree : ℝ) ≤ d := Nat.cast_le.mpr hpdeg
    linarith
  have hcoeff :
      0 < (eulerInsertionStep c d p).coeff (p.natDegree + 1) := by
    rw [coeff_eulerInsertionStep_succ]
    rw [coeff_eq_zero_of_natDegree_lt (by lia)]
    simp only [mul_zero, zero_add]
    change 0 < ((d : ℝ) + 1 - p.natDegree) * p.leadingCoeff
    exact mul_pos hfactor hp_pos
  have hdeg : (eulerInsertionStep c d p).natDegree = p.natDegree + 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_eulerInsertionStep_le c d p) hcoeff.ne'
  refine ⟨hdeg, ?_⟩
  rw [HasPosLeadingCoeff, leadingCoeff, hdeg]
  exact hcoeff

/-- Nonnegative boundary and coefficient weights preserve coefficient
nonnegativity up to the declared degree bound. -/
theorem HasNonnegCoeffs.eulerInsertionStep
    {c : ℝ} {d : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hc : 0 ≤ c) (hpdeg : p.natDegree ≤ d) :
    HasNonnegCoeffs (eulerInsertionStep c d p) := by
  intro k
  cases k with
  | zero =>
      rw [coeff_eulerInsertionStep_zero]
      exact mul_nonneg hc (hp 0)
  | succ k =>
      rw [coeff_eulerInsertionStep_succ]
      by_cases hk : k ≤ d
      · have hweight : 0 ≤ (d : ℝ) + 1 - k := by
          have hcast : (k : ℝ) ≤ d := Nat.cast_le.mpr hk
          linarith
        exact add_nonneg
          (mul_nonneg (by positivity) (hp (k + 1)))
          (mul_nonneg hweight (hp k))
      · have hdk : d < k := Nat.lt_of_not_ge hk
        have hpk : p.coeff k = 0 :=
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg hdk)
        have hpks : p.coeff (k + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg (by lia))
        simp [hpk, hpks]

/-- An Euler insertion step lies immediately to the right of its input in
proper position.  The proof includes the degree-zero boundary case. -/
theorem prec_eulerInsertionStep
    {c : ℝ} {d : ℕ} {p : ℝ[X]}
  (hp : HasNonnegCoeffs p) (hp_pos : HasPosLeadingCoeff p)
    (hp_splits : p.Splits) (hpdeg : p.natDegree ≤ d) :
    Prec p (eulerInsertionStep c d p) := by
  obtain ⟨hout_deg, hout_pos⟩ :=
    eulerInsertionStep_degree_pos (c := c) hpdeg hp_pos
  by_cases hpdeg0 : p.natDegree = 0
  · have hout_deg1 : (eulerInsertionStep c d p).natDegree = 1 := by lia
    exact prec_degree_zero_right_of_degree_one
      hp_pos.ne_zero hp_splits hout_pos.ne_zero
      (Polynomial.Splits.of_natDegree_le_one (by lia)) hpdeg0 hout_deg1
  · have hpdeg_pos : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hpdeg0
    have hder : Interlaces p.derivative p :=
      interlaces_derivative_of_pos_natDegree
        hp_pos.ne_zero hp_splits hp_pos hpdeg_pos
    have hder_pos : HasPosLeadingCoeff p.derivative :=
      hp_pos.derivative hpdeg0
    rw [eulerInsertionStep_eq]
    refine prec_of_interlaces_evalCoeff_nonpos
      hder hder_pos ?_ ?_ ?_ ?_
    · rw [← eulerInsertionStep_eq]
      exact hout_pos
    · rw [← eulerInsertionStep_eq, hout_deg]
      lia
    · rw [← eulerInsertionStep_eq, hout_deg]
    · intro r hr
      have hr_nonpos : r ≤ 0 :=
        roots_nonpos_of_hasNonnegCoeffs hp r
          ((mem_roots hp_pos.ne_zero).mpr hr)
      simp only [eval_sub, eval_X, eval_pow]
      nlinarith [sq_nonneg r]

theorem splits_eulerInsertionStep
    {c : ℝ} {d : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hp_pos : HasPosLeadingCoeff p)
    (hp_splits : p.Splits) (hpdeg : p.natDegree ≤ d) :
    (eulerInsertionStep c d p).Splits :=
  (prec_eulerInsertionStep hp hp_pos hp_splits hpdeg).2.1.2

/-- Applying one fixed nonnegative-boundary Euler insertion step to both
members of a compatible nonnegative pair preserves compatibility. -/
theorem Compatible.map_eulerInsertionStep
    {c : ℝ} {d : ℕ} {f g : ℝ[X]}
    (hfg : Compatible f g)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hfdeg : f.natDegree ≤ d) (hgdeg : g.natDegree ≤ d) :
    Compatible (eulerInsertionStep c d f) (eulerInsertionStep c d g) := by
  intro α β hα hβ
  let p := C α * f + C β * g
  have hp : HasNonnegCoeffs p := by
    intro k
    dsimp [p]
    simp only [coeff_add, coeff_C_mul]
    exact add_nonneg (mul_nonneg hα (hf k)) (mul_nonneg hβ (hg k))
  have hpdeg : p.natDegree ≤ d := by
    exact (natDegree_add_le _ _).trans <|
      max_le ((natDegree_C_mul_le α f).trans hfdeg)
        ((natDegree_C_mul_le β g).trans hgdeg)
  have hlinear :
      C α * eulerInsertionStep c d f + C β * eulerInsertionStep c d g =
        eulerInsertionStep c d p := by
    rw [eulerInsertionStep_add, eulerInsertionStep_C_mul,
      eulerInsertionStep_C_mul]
  rw [hlinear]
  rcases hfg α β hα hβ with hp_zero | hp_rr
  · left
    simp [p, hp_zero]
  · right
    have hp_pos : HasPosLeadingCoeff p :=
      hp.pos_leadingCoeff hp_rr.1
    exact ⟨(eulerInsertionStep_degree_pos hpdeg hp_pos).2.ne_zero,
      splits_eulerInsertionStep hp hp_pos hp_rr.2 hpdeg⟩

/-! ## A real partial-fraction evaluation lemma -/

private theorem eval_divByMonic_X_sub_C_div_eval
    {p : ℝ[X]} {s x : ℝ} (hs : p.IsRoot s) (hx : ¬p.IsRoot x) :
    (p /ₘ (X - C s)).eval x / p.eval x = 1 / (x - s) := by
  have hfactor : (X - C s) * (p /ₘ (X - C s)) = p :=
    mul_divByMonic_eq_iff_isRoot.mpr hs
  have hpx : p.eval x ≠ 0 := by simpa [Polynomial.IsRoot.def] using hx
  have hxs : x - s ≠ 0 := by
    intro hzero
    have : x = s := sub_eq_zero.mp hzero
    exact hx (this ▸ hs)
  have heval := congrArg (Polynomial.eval x) hfactor
  simp only [eval_mul, eval_sub, eval_X, eval_C] at heval
  have hcofactor : (p /ₘ (X - C s)).eval x ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at heval
    exact hpx heval.symm
  rw [← heval]
  field_simp [hcofactor, hxs]

/-- Real evaluation of the Lagrange partial-fraction expansion. -/
private theorem eval_ratio_eq_sum_residues
    {p q : ℝ[X]} (hp_splits : p.Splits) (hp_nodup : p.roots.Nodup)
    (hpdeg : 1 ≤ p.natDegree) (hqdeg : q.degree < p.natDegree)
    {x : ℝ} (hx : ¬p.IsRoot x) :
    q.eval x / p.eval x =
      ∑ s ∈ p.roots.toFinset,
        (q.eval s / p.derivative.eval s) / (x - s) := by
  have hlag : lagInterp p q = q :=
    lagInterp_eq_g hp_splits hp_nodup hpdeg hqdeg
  nth_rewrite 1 [← hlag]
  unfold lagInterp
  rw [eval_finsetSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  have hsroot : p.IsRoot s :=
    isRoot_of_mem_roots (Multiset.mem_toFinset.mp hs)
  rw [eval_mul, eval_C, mul_div_assoc]
  rw [eval_divByMonic_X_sub_C_div_eval hsroot hx]
  ring

/-- Every nonnegative residue term is bounded by the full positive-axis
ratio.  This is the exact quantitative input in the mixed Euler argument. -/
private theorem residue_div_sub_le_eval_ratio
    {h g : ℝ[X]} (hgh : Prec g h)
    (hh : HasNonnegCoeffs h) (hh_pos : HasPosLeadingCoeff h)
    (hg_pos : HasPosLeadingCoeff g)
    (hh_nodup : h.roots.Nodup) (hg_nodup : g.roots.Nodup)
    (hno : ∀ s ∈ h.roots, s ∉ g.roots)
    (hhdeg : 1 ≤ h.natDegree)
    {r x : ℝ} (hr : r ∈ h.roots) (hx : 0 ≤ x) (hheval : 0 < h.eval x) :
    (g.eval r / h.derivative.eval r) / (x - r) ≤ g.eval x / h.eval x := by
  have hxroot : ¬h.IsRoot x := by
    simp only [Polynomial.IsRoot.def]
    exact hheval.ne'
  have hroots_nonpos : ∀ s ∈ h.roots, s ≤ 0 :=
    roots_nonpos_of_hasNonnegCoeffs hh
  have hdenom_pos : ∀ s ∈ h.roots, 0 < x - s := by
    intro s hs
    have hs_nonpos := hroots_nonpos s hs
    have hne : x ≠ s := by
      intro hxs
      exact hxroot (hxs ▸ isRoot_of_mem_roots hs)
    exact lt_of_le_of_ne (sub_nonneg.mpr (hs_nonpos.trans hx))
      (Ne.symm (sub_ne_zero.mpr hne))
  have hres_nonneg : ∀ s ∈ h.roots,
      0 ≤ g.eval s / h.derivative.eval s := by
    intro s hs
    exact residue_nonneg hgh hh_pos hg_pos hh_nodup hg_nodup s hs (hno s hs)
  by_cases hdeg : g.natDegree = h.natDegree
  · let c₀ : ℝ := g.leadingCoeff / h.leadingCoeff
    let q : ℝ[X] := g - C c₀ * h
    have hc₀_nonneg : 0 ≤ c₀ := by
      dsimp [c₀]
      exact (div_pos hg_pos hh_pos).le
    have hqdeg : q.degree < h.natDegree := by
      exact degree_sub_c₀_mul_lt
        hh_pos.ne_zero hg_pos.ne_zero hdeg hh_pos
    have hqroot : ∀ s, h.IsRoot s → q.eval s = g.eval s := by
      intro s hs
      simp [q, Polynomial.IsRoot.def.mp hs]
    have hratio :=
      eval_ratio_eq_sum_residues hgh.2.1.2 hh_nodup hhdeg hqdeg hxroot
    have hsum_le :
        (q.eval r / h.derivative.eval r) / (x - r) ≤
          ∑ s ∈ h.roots.toFinset,
            (q.eval s / h.derivative.eval s) / (x - s) := by
      refine Finset.single_le_sum
        (s := h.roots.toFinset)
        (f := fun s => (q.eval s / h.derivative.eval s) / (x - s)) ?_ ?_
      · intro s hs
        have hsroots : s ∈ h.roots := Multiset.mem_toFinset.mp hs
        rw [hqroot s (isRoot_of_mem_roots hsroots)]
        exact div_nonneg (hres_nonneg s hsroots) (hdenom_pos s hsroots).le
      · exact Multiset.mem_toFinset.mpr hr
    rw [hqroot r (isRoot_of_mem_roots hr)] at hsum_le
    rw [← hratio] at hsum_le
    have hqeval : q.eval x = g.eval x - c₀ * h.eval x := by
      simp [q]
    rw [hqeval] at hsum_le
    have hheval_ne : h.eval x ≠ 0 := hheval.ne'
    have hrewrite :
        (g.eval x - c₀ * h.eval x) / h.eval x =
          g.eval x / h.eval x - c₀ := by
      field_simp
    rw [hrewrite] at hsum_le
    linarith
  · have hdeg_lt : g.natDegree < h.natDegree :=
      lt_of_le_of_ne hgh.natDegree_le hdeg
    have hgdeg : g.degree < h.natDegree := by
      rw [degree_eq_natDegree hg_pos.ne_zero]
      exact_mod_cast hdeg_lt
    have hratio :=
      eval_ratio_eq_sum_residues hgh.2.1.2 hh_nodup hhdeg hgdeg hxroot
    have hsum_le :
        (g.eval r / h.derivative.eval r) / (x - r) ≤
          ∑ s ∈ h.roots.toFinset,
            (g.eval s / h.derivative.eval s) / (x - s) := by
      refine Finset.single_le_sum
        (s := h.roots.toFinset)
        (f := fun s => (g.eval s / h.derivative.eval s) / (x - s)) ?_ ?_
      · intro s hs
        have hsroots : s ∈ h.roots := Multiset.mem_toFinset.mp hs
        exact div_nonneg (hres_nonneg s hsroots) (hdenom_pos s hsroots).le
      · exact Multiset.mem_toFinset.mpr hr
    simpa [hratio] using hsum_le

/-- If the right polynomial has at least two roots, every individual residue
term is strictly smaller than the full ratio at zero. -/
private theorem residue_div_neg_lt_eval_ratio_of_natDegree_ge_two
    {h g : ℝ[X]} (hgh : Prec g h)
    (hh : HasNonnegCoeffs h) (hh_pos : HasPosLeadingCoeff h)
    (hg_pos : HasPosLeadingCoeff g)
    (hh_nodup : h.roots.Nodup) (hg_nodup : g.roots.Nodup)
    (hno : ∀ s ∈ h.roots, s ∉ g.roots)
    (hhdeg : 2 ≤ h.natDegree) (hgdeg : g.natDegree < h.natDegree)
    {r : ℝ} (hr : r ∈ h.roots) (hheval : 0 < h.eval 0) :
    (g.eval r / h.derivative.eval r) / (-r) < g.eval 0 / h.eval 0 := by
  have hxroot : ¬h.IsRoot 0 := by
    simp only [Polynomial.IsRoot.def]
    exact hheval.ne'
  have hgdegree : g.degree < h.natDegree := by
    rw [degree_eq_natDegree hg_pos.ne_zero]
    exact_mod_cast hgdeg
  have hratio :=
    eval_ratio_eq_sum_residues hgh.2.1.2 hh_nodup (by lia) hgdegree hxroot
  have hcard : 2 ≤ h.roots.toFinset.card := by
    rw [Multiset.toFinset_card_of_nodup hh_nodup,
      card_roots_of_splits hgh.2.1.2]
    exact hhdeg
  obtain ⟨s, hs, hsr⟩ := h.roots.toFinset.exists_mem_ne (by lia) r
  have hsroots : s ∈ h.roots := Multiset.mem_toFinset.mp hs
  have hroots_nonpos := roots_nonpos_of_hasNonnegCoeffs hh
  have hs_neg : s < 0 := by
    have hs_nonpos := hroots_nonpos s hsroots
    have hs_ne : s ≠ 0 := by
      intro hs0
      exact hxroot (hs0 ▸ isRoot_of_mem_roots hsroots)
    exact lt_of_le_of_ne hs_nonpos hs_ne
  have hterm_pos :
      0 < (g.eval s / h.derivative.eval s) / (-s) := by
    have hprod := residue_sign_pos hgh hh_pos hg_pos hh_nodup hg_nodup
      s hsroots (hno s hsroots)
    have hrespos : 0 < g.eval s / h.derivative.eval s :=
      (div_pos_iff.mpr (mul_pos_iff.mp hprod))
    exact div_pos hrespos (by linarith)
  have hterm_nonneg : ∀ t ∈ h.roots.toFinset, t ≠ r →
      0 ≤ (g.eval t / h.derivative.eval t) / (-t) := by
    intro t ht _
    have htroots : t ∈ h.roots := Multiset.mem_toFinset.mp ht
    have ht_nonpos := hroots_nonpos t htroots
    have ht_ne : t ≠ 0 := by
      intro ht0
      exact hxroot (ht0 ▸ isRoot_of_mem_roots htroots)
    exact div_nonneg
      (residue_nonneg hgh hh_pos hg_pos hh_nodup hg_nodup
        t htroots (hno t htroots)) (by linarith)
  have hstrict :
      (g.eval r / h.derivative.eval r) / (-r) <
        ∑ t ∈ h.roots.toFinset,
          (g.eval t / h.derivative.eval t) / (-t) := by
    exact Finset.single_lt_sum hsr (Multiset.mem_toFinset.mpr hr) hs
      hterm_pos hterm_nonneg
  simpa [sub_eq_add_neg, hratio] using hstrict

/-! ## The strict mixed adjacent step -/

theorem eulerInsertionStep_one_eq_zero_succ_add
    (n : ℕ) (p : ℝ[X]) :
    eulerInsertionStep 1 n p =
      eulerInsertionStep 0 (n + 1) p + (1 - X) * p := by
  simp [eulerInsertionStep]
  ring

private theorem mixedEulerStep_eq
    (n : ℕ) (lam : ℝ) (f g : ℝ[X]) :
    eulerInsertionStep 0 (n + 1) f +
        C lam * eulerInsertionStep 1 n g =
      eulerInsertionStep 0 (n + 1) (f + C lam * g) +
        C lam * ((1 - X) * g) := by
  rw [eulerInsertionStep_add, eulerInsertionStep_C_mul,
    eulerInsertionStep_one_eq_zero_succ_add]
  ring

/-- Strict core of the mixed adjacent Euler lemma.  The right input has one
more degree, the two inputs have no common root, and its constant coefficient
is positive. -/
private theorem mixedEulerStep_prec_of_no_common_of_nontrivial_boundary
    {n : ℕ} {lam : ℝ} {f g : ℝ[X]}
    (hlam : 0 < lam)
    (hgf : Prec g f)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hg_splits : g.Splits)
    (hdeg : g.natDegree + 1 = f.natDegree)
    (hfdeg : f.natDegree ≤ n + 1)
    (hno : ∀ r, f.IsRoot r → ¬g.IsRoot r)
    (hfboundary : 0 < f.coeff 0 ∨ 2 ≤ f.natDegree) :
    Prec (f + C lam * g)
      (eulerInsertionStep 0 (n + 1) f +
        C lam * eulerInsertionStep 1 n g) := by
  let h : ℝ[X] := f + C lam * g
  let P : ℝ[X] := eulerInsertionStep 0 (n + 1) f +
    C lam * eulerInsertionStep 1 n g
  have hh : HasNonnegCoeffs h := by
    intro k
    dsimp [h]
    simp only [coeff_add, coeff_C_mul]
    exact add_nonneg (hf k) (mul_nonneg hlam.le (hg k))
  have hh_ne : h ≠ 0 := by
    intro hzero
    have hz := congrArg (fun p : ℝ[X] => p.coeff 0) hzero
    dsimp [h] at hz
    simp only [coeff_add, coeff_C_mul] at hz
    have hgzero : 0 ≤ g.coeff 0 := hg 0
    rcases hfboundary with hfzero | hfdeg2
    · nlinarith
    · have hf_ne : f ≠ 0 := hf_pos.ne_zero
      have hg_ne : g ≠ 0 := hg_pos.ne_zero
      have heval_one : 0 < h.eval 1 := by
        dsimp [h]
        simp only [eval_add, eval_mul, eval_C]
        have hf_one := eval_pos_of_hasNonnegCoeffs hf hf_ne zero_lt_one
        have hg_one := eval_pos_of_hasNonnegCoeffs hg hg_ne zero_lt_one
        nlinarith
      simp [hzero] at heval_one
  have hh_pos : HasPosLeadingCoeff h := hh.pos_leadingCoeff hh_ne
  have hh_splits : h.Splits := by
    have hrr := isRealRooted_pos_combo_of_prec
      hgf hg_pos hf_pos hlam zero_lt_one
    simpa [h, add_comm] using hrr.2
  have hh_deg : h.natDegree = f.natDegree := by
    have hle : h.natDegree ≤ f.natDegree := by
      dsimp [h]
      exact (natDegree_add_le _ _).trans <|
        max_le le_rfl ((natDegree_C_mul_le lam g).trans (by lia))
    apply le_antisymm hle
    exact le_natDegree_of_ne_zero <| by
      rw [show h.coeff f.natDegree = f.leadingCoeff by
        dsimp [h]
        rw [coeff_add, coeff_C_mul]
        change f.leadingCoeff + lam * g.coeff f.natDegree = f.leadingCoeff
        rw [coeff_eq_zero_of_natDegree_lt (by lia), mul_zero, add_zero]]
      exact hf_pos.ne'
  have hscaled_no : ∀ r, (C lam * g).IsRoot r → ¬f.IsRoot r := by
    intro r hgr hfr
    have hgr' : g.IsRoot r := by
      simp only [Polynomial.IsRoot.def, eval_mul, eval_C] at hgr ⊢
      exact (mul_eq_zero.mp hgr).resolve_left hlam.ne'
    exact hno r hfr hgr'
  have hcop : IsCoprime (C lam * g) f :=
    isCoprime_of_no_common_real_root_of_isRealRooted
      (hasPosLeadingCoeff_C_mul hlam hg_pos).ne_zero
      (hg_splits.C_mul lam) hscaled_no
  have hgh : Prec g h := by
    have hprec := prec_convex_left hgf hg_pos hf_pos hlam zero_lt_one
      (by simpa [h, add_comm] using hh_ne)
      (by simpa [h, add_comm] using hh_splits) (by simpa using hcop)
    simpa [h, add_comm] using hprec
  have hno_hg : ∀ r, h.IsRoot r → ¬g.IsRoot r := by
    intro r hhr hgr
    apply hno r
    · change (f + C lam * g).eval r = 0 at hhr
      change g.eval r = 0 at hgr
      change f.eval r = 0
      simpa [hgr] using hhr
    · exact hgr
  have hf_nodup : f.roots.Nodup := by
    by_contra hdup
    obtain ⟨r, hrf, hrg⟩ := exists_common_root_of_not_nodup hgf hdup
    exact hno r (isRoot_of_mem_roots hrf) (isRoot_of_mem_roots hrg)
  have hg_nodup : g.roots.Nodup := by
    by_contra hdup
    obtain ⟨r, hrf, hrg⟩ := exists_common_root_of_not_nodup_g hgf hdup
    exact hno r (isRoot_of_mem_roots hrf) (isRoot_of_mem_roots hrg)
  have hh_nodup : h.roots.Nodup := by
    by_contra hdup
    obtain ⟨r, hrh, hrg⟩ := exists_common_root_of_not_nodup hgh hdup
    exact hno_hg r (isRoot_of_mem_roots hrh) (isRoot_of_mem_roots hrg)
  have hhdeg_pos : 1 ≤ h.natDegree := by
    rw [hh_deg, ← hdeg]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hfdeg_step : f.natDegree ≤ n + 1 := hfdeg
  have hgdeg_step : g.natDegree ≤ n := by lia
  have hEf_nonneg : HasNonnegCoeffs (eulerInsertionStep 0 (n + 1) f) :=
    hf.eulerInsertionStep (by norm_num) hfdeg_step
  have hEg_nonneg : HasNonnegCoeffs (eulerInsertionStep 1 n g) :=
    hg.eulerInsertionStep (by norm_num) hgdeg_step
  have hP : HasNonnegCoeffs P := by
    intro k
    dsimp [P]
    simp only [coeff_add, coeff_C_mul]
    exact add_nonneg (hEf_nonneg k) (mul_nonneg hlam.le (hEg_nonneg k))
  have hP_ne : P ≠ 0 := by
    have hEf_pos :=
      (eulerInsertionStep_degree_pos (c := (0 : ℝ)) hfdeg_step hf_pos).2
    intro hzero
    have heval := congrArg (Polynomial.eval 1) hzero
    dsimp [P] at heval
    simp only [eval_add, eval_mul, eval_C] at heval
    have hEf_eval : 0 < (eulerInsertionStep 0 (n + 1) f).eval 1 :=
      eval_pos_of_hasNonnegCoeffs hEf_nonneg hEf_pos.ne_zero zero_lt_one
    have hEg_pos :=
      (eulerInsertionStep_degree_pos (c := (1 : ℝ)) hgdeg_step hg_pos).2
    have hEg_eval : 0 < (eulerInsertionStep 1 n g).eval 1 :=
      eval_pos_of_hasNonnegCoeffs hEg_nonneg hEg_pos.ne_zero zero_lt_one
    simp only [eval_zero] at heval
    nlinarith
  have hP_pos : HasPosLeadingCoeff P := hP.pos_leadingCoeff hP_ne
  have hP_deg : P.natDegree = h.natDegree + 1 := by
    have hle : P.natDegree ≤ h.natDegree + 1 := by
      dsimp [P]
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · rw [hh_deg]
        exact natDegree_eulerInsertionStep_le 0 (n + 1) f
      · exact (natDegree_C_mul_le lam _).trans <| by
          rw [hh_deg]
          exact (natDegree_eulerInsertionStep_le 1 n g).trans (by lia)
    have hcoeffEf :
        0 < (eulerInsertionStep 0 (n + 1) f).coeff (f.natDegree + 1) := by
      obtain ⟨hEfdeg, hEfpos⟩ :=
        eulerInsertionStep_degree_pos (c := (0 : ℝ)) hfdeg_step hf_pos
      unfold HasPosLeadingCoeff at hEfpos
      rw [Polynomial.leadingCoeff, hEfdeg] at hEfpos
      exact hEfpos
    have hcoeffP : 0 < P.coeff (h.natDegree + 1) := by
      rw [hh_deg]
      dsimp [P]
      rw [coeff_add, coeff_C_mul]
      exact add_pos_of_pos_of_nonneg hcoeffEf
        (mul_nonneg hlam.le (hEg_nonneg (f.natDegree + 1)))
    exact natDegree_eq_of_le_of_coeff_ne_zero hle hcoeffP.ne'
  have hder : Interlaces h.derivative h :=
    interlaces_derivative_of_pos_natDegree
      hh_ne hh_splits hh_pos hhdeg_pos
  have hder_pos : HasPosLeadingCoeff h.derivative :=
    hh_pos.derivative (by lia)
  have hroot_sign : ∀ r, h.IsRoot r → P.eval r * h.derivative.eval r < 0 := by
    intro r hroot
    have hrmem : r ∈ h.roots := (mem_roots hh_ne).mpr hroot
    have hr_nonpos := roots_nonpos_of_hasNonnegCoeffs hh r hrmem
    have hhzero : 0 < h.eval 0 := by
      have hfeval : 0 ≤ f.eval 0 := by
        simpa [coeff_zero_eq_eval_zero] using hf 0
      have hgeval : 0 ≤ g.eval 0 := by
        simpa [coeff_zero_eq_eval_zero] using hg 0
      have hsum_ne : f.eval 0 + lam * g.eval 0 ≠ 0 := by
        intro hsum
        have hf0 : f.eval 0 = 0 := by nlinarith
        have hg0 : g.eval 0 = 0 := by nlinarith
        exact hno 0 (by simpa [Polynomial.IsRoot.def] using hf0)
          (by simpa [Polynomial.IsRoot.def] using hg0)
      dsimp [h]
      simp only [eval_add, eval_mul, eval_C]
      exact lt_of_le_of_ne (add_nonneg hfeval (mul_nonneg hlam.le hgeval))
        (Ne.symm hsum_ne)
    have hr_neg : r < 0 := by
      have hr_ne : r ≠ 0 := by
        intro hr0
        have := Polynomial.IsRoot.def.mp hroot
        rw [hr0] at this
        exact hhzero.ne' this
      exact lt_of_le_of_ne hr_nonpos hr_ne
    let residue : ℝ := g.eval r / h.derivative.eval r
    have hres_nonneg : 0 ≤ residue := by
      exact residue_nonneg hgh hh_pos hg_pos hh_nodup hg_nodup r hrmem
        (by
          intro hrg
          exact hno_hg r hroot (isRoot_of_mem_roots hrg))
    have hno_roots : ∀ s ∈ h.roots, s ∉ g.roots := fun s hs => by
      intro hsg
      exact hno_hg s (isRoot_of_mem_roots hs) (isRoot_of_mem_roots hsg)
    have hf_eval_zero : 0 ≤ f.eval 0 := by
      simpa [coeff_zero_eq_eval_zero] using hf 0
    have hg_eval_zero : 0 ≤ g.eval 0 := by
      simpa [coeff_zero_eq_eval_zero] using hg 0
    have hh_eval_zero : h.eval 0 = f.eval 0 + lam * g.eval 0 := by
      simp [h]
    have hbound : r + lam * residue < 0 := by
      rcases hfboundary with hfzero | hfdeg2
      · have hratio := residue_div_sub_le_eval_ratio hgh hh hh_pos hg_pos
          hh_nodup hg_nodup hno_roots hhdeg_pos hrmem (le_refl 0) hhzero
        have hcross : residue * h.eval 0 ≤ g.eval 0 * (-r) := by
          have hnegpos : 0 < -r := by linarith
          exact (div_le_div_iff₀ hnegpos hhzero).mp
            (by simpa [residue] using hratio)
        have hf_eval_pos : 0 < f.eval 0 := by
          simpa [coeff_zero_eq_eval_zero] using hfzero
        nlinarith
      · have hratio :=
          residue_div_neg_lt_eval_ratio_of_natDegree_ge_two
            hgh hh hh_pos hg_pos hh_nodup hg_nodup hno_roots
            (by rw [hh_deg]; exact hfdeg2) (by rw [hh_deg]; lia)
            hrmem hhzero
        have hcross : residue * h.eval 0 < g.eval 0 * (-r) := by
          have hnegpos : 0 < -r := by linarith
          exact (div_lt_div_iff₀ hnegpos hhzero).mp
            (by simpa [residue] using hratio)
        nlinarith
    have hder_ne : h.derivative.eval r ≠ 0 := by
      exact derivative_eval_ne_zero_of_simple_root hroot <|
        by simpa [count_roots] using Multiset.count_eq_one_of_mem hh_nodup hrmem
    have hgres : g.eval r = residue * h.derivative.eval r := by
      dsimp [residue]
      field_simp
    have hidentity :
        P.eval r = (1 - r) * h.derivative.eval r * (r + lam * residue) := by
      change
        (eulerInsertionStep 0 (n + 1) f +
          C lam * eulerInsertionStep 1 n g).eval r = _
      rw [mixedEulerStep_eq n lam f g]
      change
        (eulerInsertionStep 0 (n + 1) h + C lam * ((1 - X) * g)).eval r = _
      simp only [eval_add, eval_mul, eval_C, eulerInsertionStep_eq,
        eval_sub, eval_one, eval_X, eval_pow, Polynomial.IsRoot.def.mp hroot]
      rw [hgres]
      ring
    rw [hidentity]
    have hone : 0 < 1 - r := by linarith
    have hprod : (1 - r) * (r + lam * residue) < 0 :=
      mul_neg_of_pos_of_neg hone hbound
    calc
      (1 - r) * h.derivative.eval r * (r + lam * residue) *
          h.derivative.eval r =
        ((1 - r) * (r + lam * residue)) * (h.derivative.eval r) ^ 2 := by ring
      _ < 0 := mul_neg_of_neg_of_pos hprod (sq_pos_of_ne_zero hder_ne)
  exact prec_of_interlaces_eval_mul_neg_succ hder hder_pos hP_pos hP_deg hroot_sign

/-- No-common-root mixed step, including the exceptional linear/constant
boundary where the mixed output has the input sum as an exact factor. -/
private theorem mixedEulerStep_prec_of_no_common
    {n : ℕ} {lam : ℝ} {f g : ℝ[X]}
    (hlam : 0 < lam)
    (hgf : Prec g f)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hg_splits : g.Splits)
    (hdeg : g.natDegree + 1 = f.natDegree)
    (hfdeg : f.natDegree ≤ n + 1)
    (hno : ∀ r, f.IsRoot r → ¬g.IsRoot r) :
    Prec (f + C lam * g)
      (eulerInsertionStep 0 (n + 1) f +
        C lam * eulerInsertionStep 1 n g) := by
  by_cases hfzero_pos : 0 < f.coeff 0
  · exact mixedEulerStep_prec_of_no_common_of_nontrivial_boundary
      hlam hgf hf hg hf_pos hg_pos hg_splits hdeg hfdeg hno (Or.inl hfzero_pos)
  have hfzero_nonneg : 0 ≤ f.coeff 0 := hf 0
  have hfzero : f.coeff 0 = 0 := by linarith
  by_cases hfdeg2 : 2 ≤ f.natDegree
  · exact mixedEulerStep_prec_of_no_common_of_nontrivial_boundary
      hlam hgf hf hg hf_pos hg_pos hg_splits hdeg hfdeg hno (Or.inr hfdeg2)
  have hfdeg1 : f.natDegree = 1 := by lia
  have hgdeg0 : g.natDegree = 0 := by lia
  have hfform : f = C f.leadingCoeff * X := by
    ext k
    cases k with
    | zero => simp [hfzero]
    | succ k =>
        cases k with
        | zero => simp [Polynomial.leadingCoeff, hfdeg1]
        | succ k =>
            have hk : f.natDegree < k + 2 := by lia
            rw [coeff_eq_zero_of_natDegree_lt hk]
            simp
  have hgzero : g.coeff 0 = g.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hgdeg0]
  have hgform : g = C g.leadingCoeff := by
    calc
      g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero hgdeg0
      _ = C g.leadingCoeff := congrArg C hgzero
  let h : ℝ[X] := f + C lam * g
  let P : ℝ[X] := eulerInsertionStep 0 (n + 1) f +
    C lam * eulerInsertionStep 1 n g
  have hh_ne : h ≠ 0 := by
    intro hzero
    have hz := congrArg (fun p : ℝ[X] => p.coeff 0) hzero
    dsimp [h] at hz
    simp only [coeff_add, coeff_C_mul] at hz
    rw [hfzero, hgzero] at hz
    have hglc : 0 < g.leadingCoeff := hg_pos
    nlinarith
  have hh_splits : h.Splits := by
    have hrr := isRealRooted_pos_combo_of_prec
      hgf hg_pos hf_pos hlam zero_lt_one
    simpa [h, add_comm] using hrr.2
  let c : ℝ := (n : ℝ) + 1
  let u : ℝ := -c⁻¹
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hPfactor0 : P = (1 + C c * X) * h := by
    dsimp [P, h, c]
    rw [hfform, hgform]
    simp [eulerInsertionStep]
    ring
  have hlinear : (1 + C c * X : ℝ[X]) = C c * (X - C u) := by
    dsimp [u]
    calc
      1 + C c * X = C c * X + 1 := by ring
      _ = C c * (X - C (-c⁻¹)) := by
        rw [mul_sub]
        rw [show C (-c⁻¹) = -(C c⁻¹ : ℝ[X]) by simp]
        rw [mul_neg, show C c * C c⁻¹ = (1 : ℝ[X]) by
          rw [← C_mul]
          simp [hc_ne]]
        ring
  have hPfactor : P = C c * ((X - C u) * h) := by
    rw [hPfactor0, hlinear]
    ring
  have hbase : Prec h ((X - C u) * h) :=
    prec_self_X_sub_C_mul hh_ne hh_splits u
  have hscaled : Prec h (C c * ((X - C u) * h)) :=
    prec_C_mul_right hbase hc_pos.ne'
  rw [← hPfactor] at hscaled
  exact hscaled

end RealRooted
