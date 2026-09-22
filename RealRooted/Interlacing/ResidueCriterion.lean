import RealRooted.Interlacing.Residue
import RealRooted.Interlacing.OuterDifference
import RealRooted.MaWang.StrictSigns
import RealRooted.SimpleRoots

/-!
# A positive-point residue criterion for strict interlacing

Lagrange interpolation expresses a lower-degree polynomial divided by a split
polynomial as a finite sum of its residues. For a positive-leading proper-
position pair, those residues are nonnegative. A strict evaluation gap at a
point to the right of every root therefore bounds each residue separately.

The final theorem applies this bound to
`degree(f) * f + (a - X) * f' - m * g`. It proves the leading-term
cancellation and turns strict signs at the roots of `f` into an `Interlaces`
certificate.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted

/-- Lagrange residue expansion of `g(a) / f(a)` when `g` has smaller degree. -/
theorem eval_div_eq_sum_residue_div
    {f g : ℝ[X]} (hf : f.Splits) (hfnd : f.roots.Nodup)
    (hfdeg : 1 ≤ f.natDegree) (hgdeg : g.degree < f.natDegree)
    {a : ℝ} (hfa : f.eval a ≠ 0) :
    g.eval a / f.eval a =
      ∑ r ∈ f.roots.toFinset,
        (g.eval r / f.derivative.eval r) / (a - r) := by
  have hlag := lagInterp_eq_g hf hfnd hfdeg hgdeg
  calc
    g.eval a / f.eval a = (lagInterp f g).eval a / f.eval a := by rw [hlag]
    _ = _ := by
      rw [lagInterp, eval_finsetSum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r hr
      have hrroot : f.IsRoot r :=
        isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
      have hfactor := mul_divByMonic_eq_iff_isRoot.mpr hrroot
      have heval := congrArg (Polynomial.eval a) hfactor
      simp only [eval_mul, eval_sub, eval_X, eval_C] at heval
      have har : a - r ≠ 0 := by
        intro har0
        have har : a = r := sub_eq_zero.mp har0
        rw [har] at hfa
        exact hfa hrroot
      simp only [eval_mul, eval_C]
      apply (div_eq_div_iff hfa har).2
      rw [← heval]
      ring

/-- At each simple root of the right polynomial, the residue of a
positive-leading left interlacer is nonnegative.  The left polynomial need not
have simple roots or be coprime to the right polynomial; a common root gives a
zero residue. -/
theorem residue_nonneg_of_right_nodup
    {f g : ℝ[X]} (hgf : StrictInterl g f)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfnd : f.roots.Nodup) (s : ℝ) (hsf : s ∈ f.roots) :
    0 ≤ g.eval s / f.derivative.eval s := by
  have hsroot : f.IsRoot s := isRoot_of_mem_roots hsf
  have hprod : 0 ≤ g.eval s * f.derivative.eval s :=
    hgf.eval_mul_derivative_nonneg_of_right_root hglc hflc hsroot
  have hmult : f.rootMultiplicity s = 1 := by
    simpa [count_roots] using Multiset.count_eq_one_of_mem hfnd hsf
  have hder_ne : f.derivative.eval s ≠ 0 :=
    eval_derivative_ne_zero_of_rootMultiplicity_eq_one hsroot hmult
  rcases lt_or_gt_of_ne hder_ne with hder_neg | hder_pos
  · exact div_nonneg_of_nonpos (by nlinarith) hder_neg.le
  · exact div_nonneg (by nlinarith) hder_pos.le

/-- A positive evaluation gap bounds every individual nonnegative residue. -/
theorem mul_residue_lt_sub_of_eval_lt
    {f g : ℝ[X]} (hgf : StrictInterl g f)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfnd : f.roots.Nodup)
    (hfdeg : 1 ≤ f.natDegree) (hgdeg : g.degree < f.natDegree)
    {a m : ℝ} (hm : 0 ≤ m)
    (ha : ∀ r ∈ f.roots, r < a) (hgap : m * g.eval a < f.eval a)
    {r : ℝ} (hr : r ∈ f.roots) :
    m * (g.eval r / f.derivative.eval r) < a - r := by
  have hfa : 0 < f.eval a :=
    eval_pos_of_all_roots_lt hgf.2.1.1 hgf.2.1.2 hflc ha
  have hsum := eval_div_eq_sum_residue_div
    hgf.2.1.2 hfnd hfdeg hgdeg hfa.ne'
  have hterm_nonneg : ∀ s ∈ f.roots.toFinset,
      0 ≤ (g.eval s / f.derivative.eval s) / (a - s) := by
    intro s hs
    have hsroots : s ∈ f.roots := Multiset.mem_toFinset.mp hs
    have hden : 0 < a - s := by linarith [ha s hsroots]
    exact div_nonneg
      (residue_nonneg_of_right_nodup hgf hflc hglc hfnd s hsroots) hden.le
  have hrfin : r ∈ f.roots.toFinset := Multiset.mem_toFinset.mpr hr
  have hle :
      (g.eval r / f.derivative.eval r) / (a - r) ≤
        ∑ s ∈ f.roots.toFinset,
          (g.eval s / f.derivative.eval s) / (a - s) := by
    exact Finset.single_le_sum (fun s hs => hterm_nonneg s hs) hrfin
  have hsum_lt : m * (g.eval a / f.eval a) < 1 := by
    rw [mul_div]
    exact (div_lt_one hfa).2 hgap
  have hterm_lt :
      m * ((g.eval r / f.derivative.eval r) / (a - r)) < 1 := by
    rw [hsum] at hsum_lt
    exact (mul_le_mul_of_nonneg_left hle hm).trans_lt hsum_lt
  have hden : 0 < a - r := by linarith [ha r hr]
  have hterm_lt' :
      (m * (g.eval r / f.derivative.eval r)) / (a - r) < 1 := by
    calc
      (m * (g.eval r / f.derivative.eval r)) / (a - r) =
          m * ((g.eval r / f.derivative.eval r) / (a - r)) := by ring
      _ < 1 := hterm_lt
  exact (div_lt_one hden).1 hterm_lt'

/-- The degree-dropping residue auxiliary attached to `f`, `g`, a point `a`,
and a nonnegative weight `m`. -/
def residueAuxiliary (a m : ℝ) (f g : ℝ[X]) : ℝ[X] :=
  C (f.natDegree : ℝ) * f + (C a - X) * f.derivative - C m * g

/-- The degree term in `residueAuxiliary` cancels the leading term contributed
by `-X * f'`. -/
theorem residueAuxiliary_degree_lt
    {f g : ℝ[X]} (hfdeg : 1 ≤ f.natDegree)
    (hgdeg : g.degree < f.natDegree) (a m : ℝ) :
    (residueAuxiliary a m f g).degree < f.natDegree := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro j hj
  rw [residueAuxiliary, coeff_sub, coeff_add, coeff_C_mul]
  have hrewrite :
      (C a - X) * f.derivative =
        C a * f.derivative - X * f.derivative := by ring
  rw [hrewrite, coeff_sub, coeff_C_mul]
  rcases eq_or_lt_of_le hj with rfl | hj
  · have hdertop : f.derivative.coeff f.natDegree = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [f.natDegree_derivative]
      lia
    have hindex : f.natDegree - 1 + 1 = f.natDegree := by lia
    have hcast : ((f.natDegree - 1 : ℕ) : ℝ) + 1 = f.natDegree := by
      exact_mod_cast hindex
    have hXder :
        (X * f.derivative).coeff f.natDegree =
          f.derivative.coeff (f.natDegree - 1) := by
      conv_lhs => rw [← hindex]
      rw [coeff_X_mul]
    have hdercoeff :
        f.derivative.coeff (f.natDegree - 1) =
          (f.natDegree : ℝ) * f.leadingCoeff := by
      rw [coeff_derivative, hindex, show f.coeff f.natDegree =
        f.leadingCoeff by rfl, hcast]
      ring
    have hgzero : g.coeff f.natDegree = 0 :=
      coeff_eq_zero_of_degree_lt hgdeg
    rw [hdertop, hXder, hdercoeff, coeff_C_mul, hgzero]
    change (f.natDegree : ℝ) * f.leadingCoeff +
      (a * 0 - (f.natDegree : ℝ) * f.leadingCoeff) - m * 0 = 0
    ring
  · have hfzero : f.coeff j = 0 := coeff_eq_zero_of_natDegree_lt hj
    have hderzero : f.derivative.coeff j = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [f.natDegree_derivative]
      lia
    have hXderzero : (X * f.derivative).coeff j = 0 := by
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : j ≠ 0)
      rw [coeff_X_mul]
      apply coeff_eq_zero_of_natDegree_lt
      rw [f.natDegree_derivative]
      lia
    have hgzero : g.coeff j = 0 :=
      coeff_eq_zero_of_degree_lt (hgdeg.trans_le (by exact_mod_cast hj.le))
    rw [hfzero, hderzero, hXderzero, coeff_C_mul, hgzero]
    ring

/-- A positive-point evaluation gap forces the residue auxiliary to have the
same sign as `f'` at every root of `f`. -/
theorem residueAuxiliary_eval_mul_derivative_pos
    {f g : ℝ[X]} (hgf : StrictInterl g f)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfdeg : 1 ≤ f.natDegree) (hgdeg : g.degree < f.natDegree)
    (hsimple : HasSimpleRoots f)
    {a m : ℝ} (hm : 0 ≤ m)
    (ha : ∀ r ∈ f.roots, r < a) (hgap : m * g.eval a < f.eval a)
    {r : ℝ} (hr : f.IsRoot r) :
    0 < (residueAuxiliary a m f g).eval r * f.derivative.eval r := by
  have hf_ne : f ≠ 0 := by
    intro hfzero
    simp [hfzero] at hflc
  have hrmem : r ∈ f.roots := (mem_roots hf_ne).mpr hr
  have hbound := mul_residue_lt_sub_of_eval_lt hgf hflc hglc
    hsimple.roots_nodup hfdeg hgdeg hm ha hgap hrmem
  have hder_ne := hsimple.eval_derivative_ne_zero hr
  have hbound' : m * g.eval r / f.derivative.eval r < a - r := by
    calc
      m * g.eval r / f.derivative.eval r =
          m * (g.eval r / f.derivative.eval r) := by ring
      _ < a - r := hbound
  have heval :
      (residueAuxiliary a m f g).eval r =
        (a - r) * f.derivative.eval r - m * g.eval r := by
    simp [residueAuxiliary, Polynomial.IsRoot.def.mp hr]
  rw [heval]
  rcases lt_or_gt_of_ne hder_ne with hder_neg | hder_pos
  · have hmul : (a - r) * f.derivative.eval r < m * g.eval r :=
      (div_lt_iff_of_neg hder_neg).mp hbound'
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hmul) hder_neg
  · have hmul : m * g.eval r < (a - r) * f.derivative.eval r :=
      (div_lt_iff₀ hder_pos).mp hbound'
    exact mul_pos (sub_pos.mpr hmul) hder_pos

/-- Positive residue data at one point makes the degree-dropping auxiliary a
strict interlacer of `f`. -/
theorem residueAuxiliary_interlaces
    {f g : ℝ[X]} (hgf : StrictInterl g f)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfdeg : 1 ≤ f.natDegree) (hgdeg : g.degree < f.natDegree)
    (hsimple : HasSimpleRoots f)
    {a m : ℝ} (hm : 0 ≤ m)
    (ha : ∀ r ∈ f.roots, r < a) (hgap : m * g.eval a < f.eval a) :
    Interlaces (residueAuxiliary a m f g) f := by
  have hq_sign : ∀ r, f.IsRoot r →
      0 < (residueAuxiliary a m f g).eval r * f.derivative.eval r := by
    intro r hr
    exact residueAuxiliary_eval_mul_derivative_pos
      hgf hflc hglc hfdeg hgdeg hsimple hm ha hgap hr
  have hroots_ne : f.roots ≠ 0 := by
    intro hzero
    have hcard : f.roots.card = f.natDegree :=
      card_roots_of_splits hgf.2.1.2
    rw [hzero] at hcard
    simp at hcard
    lia
  obtain ⟨r, hrmem⟩ := Multiset.exists_mem_of_ne_zero hroots_ne
  have hrroot : f.IsRoot r := isRoot_of_mem_roots hrmem
  have hq_ne : residueAuxiliary a m f g ≠ 0 := by
    intro hzero
    have hsign := hq_sign r hrroot
    simp [hzero] at hsign
  have hqdeg : (residueAuxiliary a m f g).natDegree < f.natDegree :=
    (natDegree_lt_iff_degree_lt hq_ne).2
      (residueAuxiliary_degree_lt hfdeg hgdeg a m)
  apply interlaces_of_eval_mul_derivative_pos hgf.2.1.2 hflc hqdeg
  exact hq_sign

end RealRooted
