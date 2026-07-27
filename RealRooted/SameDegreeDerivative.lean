import RealRooted.Derivative
import RealRooted.PosCombo
import RealRooted.WagnerX

/-!
# Same-degree positive-combination derivative lemmas

This module records two reusable derivative facts for the same-degree
positive-combination route in the Chudnovsky--Seymour project.
-/

open Polynomial

namespace RealRooted

/-- If all roots of a split polynomial of degree at least two are bounded below
by `c`, then all roots of its derivative are bounded below by `c`.

This is the lower-bound counterpart to the common upper-bound use of
`roots_le_of_prec_right` together with `derivative_interlaces`. -/
theorem le_roots_derivative_of_le_roots {p : ℝ[X]} {c : ℝ}
    (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, c ≤ r) :
    ∀ r ∈ p.derivative.roots, c ≤ r := by
  obtain ⟨_, _, _, rs, ss, _, _, hrs_eq, hss_eq, hint⟩ :=
    derivative_interlaces hp hdeg
  intro s hs
  have hs_ss : s ∈ ss := Multiset.mem_coe.mp (by simp_all)
  have hrs_ne : rs ≠ [] := by
    rintro rfl
    have hcard : p.roots.card = p.natDegree := card_roots_of_splits hp
    have : (0 : ℕ) = p.roots.card := by
      rw [← hrs_eq]
      simp
    simp_all
  obtain ⟨r0, rs', rfl⟩ : ∃ r0 rs', rs = r0 :: rs' := by
    cases rs with
    | nil => simp_all
    | cons r0 rs' => simp
  have hr0_mem : r0 ∈ p.roots := by
    rw [← hrs_eq]
    simp
  have hc_r0 : c ≤ r0 := h r0 hr0_mem
  have hr0_le : r0 ≤ s := listInterlaces_all_ge ss rs' r0 hint s hs_ss
  linarith

/-- If all roots of a split polynomial of degree at least two are bounded above
by `c`, then all roots of its derivative are bounded above by `c`.

This is the upper-bound counterpart to `le_roots_derivative_of_le_roots`,
obtained from `roots_le_of_prec_right` applied to the interlacing witness. -/
theorem roots_derivative_le_of_roots_le {p : ℝ[X]} {c : ℝ}
    (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ≤ c) :
    ∀ r ∈ p.derivative.roots, r ≤ c :=
  roots_le_of_prec_right (derivative_interlaces hp hdeg).toPrec h

/-- **Derivative root interval preservation.** If every root of a split
polynomial of degree at least two lies in the closed interval `[u, v]`, then
every root of its derivative lies in `[u, v]` as well.

This packages the lower bound `le_roots_derivative_of_le_roots` and the upper
bound `roots_derivative_le_of_roots_le` into a single interval statement. -/
theorem roots_derivative_mem_Icc_of_roots_mem_Icc {p : ℝ[X]} {u v : ℝ}
    (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ∈ Set.Icc u v) :
    ∀ r ∈ p.derivative.roots, r ∈ Set.Icc u v := by
  intro r hr
  exact ⟨le_roots_derivative_of_le_roots hp hdeg (fun s hs => (h s hs).1) r hr,
    roots_derivative_le_of_roots_le hp hdeg (fun s hs => (h s hs).2) r hr⟩

/-- Strict lower bound: if every root of a split polynomial of degree at least
two is greater than `u`, then every root of its derivative is greater than
`u`. -/
theorem lt_roots_derivative_of_lt_roots {p : ℝ[X]} {u : ℝ}
    (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, u < r) :
    ∀ r ∈ p.derivative.roots, u < r := by
  obtain ⟨_, _, _, rs, ss, _, _, hrs_eq, hss_eq, hint⟩ :=
    derivative_interlaces hp hdeg
  intro s hs
  have hs_ss : s ∈ ss := Multiset.mem_coe.mp (by simp_all)
  have hrs_ne : rs ≠ [] := by
    rintro rfl
    have hcard : p.roots.card = p.natDegree := card_roots_of_splits hp
    have : (0 : ℕ) = p.roots.card := by
      rw [← hrs_eq]
      simp
    simp_all
  obtain ⟨r0, rs', rfl⟩ : ∃ r0 rs', rs = r0 :: rs' := by
    cases rs with
    | nil => simp_all
    | cons r0 rs' => simp
  have hr0_mem : r0 ∈ p.roots := by
    rw [← hrs_eq]
    simp
  have hu_r0 : u < r0 := h r0 hr0_mem
  have hr0_le : r0 ≤ s := listInterlaces_all_ge ss rs' r0 hint s hs_ss
  linarith

/-- Strict upper bound: if every root of a split polynomial of degree at least
two is less than `v`, then every root of its derivative is less than `v`. -/
theorem roots_derivative_lt_of_roots_lt {p : ℝ[X]} {v : ℝ}
    (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r < v) :
    ∀ r ∈ p.derivative.roots, r < v := by
  obtain ⟨_, _, _, rs, ss, hrs_sorted, _, hrs_eq, hss_eq, hint⟩ :=
    derivative_interlaces hp hdeg
  intro s hs
  have hs_ss : s ∈ ss := Multiset.mem_coe.mp (by simp_all)
  have hrs_ne : rs ≠ [] := by
    rintro rfl
    have hcard : p.roots.card = p.natDegree := card_roots_of_splits hp
    have : (0 : ℕ) = p.roots.card := by
      rw [← hrs_eq]
      simp
    simp_all
  have hlast_mem : rs.getLast hrs_ne ∈ rs := List.getLast_mem hrs_ne
  have hlast_root : rs.getLast hrs_ne ∈ p.roots := by
    rw [← hrs_eq]
    simp
  have hlt : rs.getLast hrs_ne < v := h _ hlast_root
  have hle : s ≤ rs.getLast hrs_ne :=
    listInterlaces_all_le_getLast hrs_ne hrs_sorted hint s hs_ss
  linarith

/-- Derivative root open-interval preservation. -/
theorem roots_derivative_mem_Ioo_of_roots_mem_Ioo {p : ℝ[X]} {u v : ℝ}
    (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ∈ Set.Ioo u v) :
    ∀ r ∈ p.derivative.roots, r ∈ Set.Ioo u v := by
  intro r hr
  exact ⟨lt_roots_derivative_of_lt_roots hp hdeg (fun s hs => (h s hs).1) r hr,
    roots_derivative_lt_of_roots_lt hp hdeg (fun s hs => (h s hs).2) r hr⟩

/-- Derivative root right-ray preservation. -/
theorem roots_derivative_mem_Ioi_of_roots_mem_Ioi {p : ℝ[X]} {u : ℝ}
    (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ∈ Set.Ioi u) :
    ∀ r ∈ p.derivative.roots, r ∈ Set.Ioi u :=
  lt_roots_derivative_of_lt_roots hp hdeg h

/-- Derivative root left-ray preservation. -/
theorem roots_derivative_mem_Iio_of_roots_mem_Iio {p : ℝ[X]} {v : ℝ}
    (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ∈ Set.Iio v) :
    ∀ r ∈ p.derivative.roots, r ∈ Set.Iio v :=
  roots_derivative_lt_of_roots_lt hp hdeg h

/-- Derivative root closed lower-ray preservation. -/
theorem roots_derivative_mem_Ici_of_roots_mem_Ici {p : ℝ[X]} {u : ℝ}
    (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ∈ Set.Ici u) :
    ∀ r ∈ p.derivative.roots, r ∈ Set.Ici u :=
  le_roots_derivative_of_le_roots hp hdeg h

/-- Derivative root closed upper-ray preservation. -/
theorem roots_derivative_mem_Iic_of_roots_mem_Iic {p : ℝ[X]} {v : ℝ}
    (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ∈ Set.Iic v) :
    ∀ r ∈ p.derivative.roots, r ∈ Set.Iic v :=
  roots_derivative_le_of_roots_le hp hdeg h

/-- Derivative root half-open interval `[u, v)` preservation. -/
theorem roots_derivative_mem_Ico_of_roots_mem_Ico {p : ℝ[X]} {u v : ℝ}
    (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ∈ Set.Ico u v) :
    ∀ r ∈ p.derivative.roots, r ∈ Set.Ico u v := by
  intro r hr
  exact ⟨le_roots_derivative_of_le_roots hp hdeg (fun s hs => (h s hs).1) r hr,
    roots_derivative_lt_of_roots_lt hp hdeg (fun s hs => (h s hs).2) r hr⟩

/-- Derivative root half-open interval `(u, v]` preservation. -/
theorem roots_derivative_mem_Ioc_of_roots_mem_Ioc {p : ℝ[X]} {u v : ℝ}
    (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ∈ Set.Ioc u v) :
    ∀ r ∈ p.derivative.roots, r ∈ Set.Ioc u v := by
  intro r hr
  exact ⟨lt_roots_derivative_of_lt_roots hp hdeg (fun s hs => (h s hs).1) r hr,
    roots_derivative_le_of_roots_le hp hdeg (fun s hs => (h s hs).2) r hr⟩

/-- **Same-degree bookkeeping.** Differentiation preserves a common natural
degree: if `g` and `f` share a degree, so do their derivatives.  This is the
degree-equality hypothesis needed to iterate the same-degree derivative route
(e.g. `PosComboRealRooted.derivative`). -/
theorem natDegree_derivative_eq_of_natDegree_eq {f g : ℝ[X]}
    (hdeg : g.natDegree = f.natDegree) :
    g.derivative.natDegree = f.derivative.natDegree := by simp_all

/-- Explicit-binder variant of `roots_derivative_mem_Ici_of_roots_mem_Ici`,
taking the polynomial and endpoint as explicit arguments so the endpoint-repair
route can apply it positionally without local unpacking. -/
theorem roots_derivative_mem_Ici_of_roots_mem_Ici_explicit
    (p : ℝ[X]) (u : ℝ) (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ∈ Set.Ici u) :
    ∀ r ∈ p.derivative.roots, r ∈ Set.Ici u :=
  roots_derivative_mem_Ici_of_roots_mem_Ici hp hdeg h

/-- Explicit-binder variant of `roots_derivative_mem_Iic_of_roots_mem_Iic`. -/
theorem roots_derivative_mem_Iic_of_roots_mem_Iic_explicit
    (p : ℝ[X]) (v : ℝ) (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ∈ Set.Iic v) :
    ∀ r ∈ p.derivative.roots, r ∈ Set.Iic v :=
  roots_derivative_mem_Iic_of_roots_mem_Iic hp hdeg h

/-- Explicit-binder variant of `roots_derivative_mem_Ico_of_roots_mem_Ico`. -/
theorem roots_derivative_mem_Ico_of_roots_mem_Ico_explicit
    (p : ℝ[X]) (u v : ℝ) (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ∈ Set.Ico u v) :
    ∀ r ∈ p.derivative.roots, r ∈ Set.Ico u v :=
  roots_derivative_mem_Ico_of_roots_mem_Ico hp hdeg h

/-- Explicit-binder variant of `roots_derivative_mem_Ioc_of_roots_mem_Ioc`. -/
theorem roots_derivative_mem_Ioc_of_roots_mem_Ioc_explicit
    (p : ℝ[X]) (u v : ℝ) (hp : p.Splits) (hdeg : 2 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ∈ Set.Ioc u v) :
    ∀ r ∈ p.derivative.roots, r ∈ Set.Ioc u v :=
  roots_derivative_mem_Ioc_of_roots_mem_Ioc hp hdeg h

namespace PosComboRealRooted

/-- Differentiation preserves positive-combination real-rootedness for a
same-degree pair with positive leading coefficients and positive common degree.

For each positive combination, the derivative is the corresponding positive
combination of the derivatives.  The positive common top coefficient ensures
that the original combination has positive degree, so Rolle gives splitting of
the derivative. -/
theorem derivative
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) (hpos : 1 ≤ f.natDegree) :
    PosComboRealRooted f.derivative g.derivative := by
  intro lam μ hlam hμ
  have key : C lam * f.derivative + C μ * g.derivative =
      (C lam * f + C μ * g).derivative := by
    simp
  obtain ⟨_, hp_splits⟩ := hfg (lam := lam) (μ := μ) hlam hμ
  have hfc : f.coeff f.natDegree = f.leadingCoeff := rfl
  have hgc : g.coeff f.natDegree = g.leadingCoeff := by
    have hn : f.natDegree = g.natDegree := hdeg.symm
    simp_all
  have hcoeff_pos : 0 < (C lam * f + C μ * g).coeff f.natDegree := by
    rw [coeff_add, coeff_C_mul, coeff_C_mul, hfc, hgc]
    have hf_top : 0 < lam * f.leadingCoeff := mul_pos hlam hf
    have hg_top : 0 < μ * g.leadingCoeff := mul_pos hμ hg
    linarith
  have hle : f.natDegree ≤ (C lam * f + C μ * g).natDegree :=
    le_natDegree_of_ne_zero (ne_of_gt hcoeff_pos)
  have hder_ne : (C lam * f + C μ * g).derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  rcases derivative_eq_zero_or_ne_zero_and_splits hp_splits with hzero | hsplit <;> simp_all

/-- Call-site-order variant taking degree equality as `f.natDegree = g.natDegree`. -/
theorem derivative_of_natDegree_eq
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : f.natDegree = g.natDegree) (hpos : 1 ≤ f.natDegree) :
    PosComboRealRooted f.derivative g.derivative :=
  hfg.derivative hf hg hdeg.symm hpos

end PosComboRealRooted

/-- Non-namespace wrapper for
`RealRooted.PosComboRealRooted.derivative`. -/
theorem posComboRealRooted_derivative
    {f g : ℝ[X]} (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) (hpos : 1 ≤ f.natDegree)
    (hfg : PosComboRealRooted f g) :
    PosComboRealRooted f.derivative g.derivative :=
  hfg.derivative hf hg hdeg hpos

/-- Non-namespace wrapper with the positive-combination hypothesis first and
degree equality as `f.natDegree = g.natDegree`. -/
theorem posComboRealRooted_derivative'
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : f.natDegree = g.natDegree) (hpos : 1 ≤ f.natDegree) :
    PosComboRealRooted f.derivative g.derivative :=
  hfg.derivative hf hg hdeg.symm hpos

/-- Explicit-binder applied form of `PosComboRealRooted.derivative` with the two
polynomials as explicit arguments and degree equality in the call-site order
`f.natDegree = g.natDegree`.  Handy at call sites that want to pass everything
positionally without introducing implicit-argument holes. -/
theorem posComboRealRooted_derivative_explicit
    (f g : ℝ[X]) (hfg : PosComboRealRooted f g)
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : f.natDegree = g.natDegree) (hpos : 1 ≤ f.natDegree) :
    PosComboRealRooted f.derivative g.derivative :=
  hfg.derivative hf hg hdeg.symm hpos

/-- **Iteration bundle for the same-degree derivative route.** From a
same-degree positive-combination pair with positive leading coefficients and
positive common degree, differentiation returns another such pair *together
with* the hypotheses needed to differentiate again: positive leading
coefficients of both derivatives and equality of their degrees.  This packages
the repeated endpoint-repair step so callers avoid re-deriving the bookkeeping
by hand. -/
theorem PosComboRealRooted.derivative_bundle
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) (hpos : 1 ≤ f.natDegree) :
    PosComboRealRooted f.derivative g.derivative ∧
      HasPosLeadingCoeff f.derivative ∧ HasPosLeadingCoeff g.derivative ∧
      g.derivative.natDegree = f.derivative.natDegree :=
  ⟨hfg.derivative hf hg hdeg hpos,
   hf.derivative (by lia),
   hg.derivative (by grind),
   natDegree_derivative_eq_of_natDegree_eq hdeg⟩

/-! ## Two-step derivative iteration support -/

/-- Splitting is preserved by one differentiation in degree at least two. -/
theorem splits_derivative_of_two_le_natDegree {p : ℝ[X]}
    (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    p.derivative.Splits :=
  (derivative_interlaces hp hdeg).2.1.2

/-- Degree lower bound transported across one differentiation. -/
theorem le_natDegree_derivative_of_succ_le_natDegree {p : ℝ[X]} {n : ℕ}
    (hdeg : n + 1 ≤ p.natDegree) :
    n ≤ p.derivative.natDegree := by
  rw [p.natDegree_derivative]
  lia

/-- Two-step derivative bundle for the same-degree positive-combination route. -/
theorem PosComboRealRooted.derivative_bundle_two
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) (hpos : 2 ≤ f.natDegree) :
    PosComboRealRooted f.derivative.derivative g.derivative.derivative ∧
      HasPosLeadingCoeff f.derivative.derivative ∧
      HasPosLeadingCoeff g.derivative.derivative ∧
      g.derivative.derivative.natDegree = f.derivative.derivative.natDegree := by
  obtain ⟨hfg₁, hf₁, hg₁, hdeg₁⟩ := hfg.derivative_bundle hf hg hdeg (by lia)
  have hpos₁ : 1 ≤ f.derivative.natDegree := by
    rw [f.natDegree_derivative]
    lia
  exact hfg₁.derivative_bundle hf₁ hg₁ hdeg₁ hpos₁

/-- Call-site-order variant of `PosComboRealRooted.derivative_bundle_two`. -/
theorem PosComboRealRooted.derivative_bundle_two_of_natDegree_eq
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : f.natDegree = g.natDegree) (hpos : 2 ≤ f.natDegree) :
    PosComboRealRooted f.derivative.derivative g.derivative.derivative ∧
      HasPosLeadingCoeff f.derivative.derivative ∧
      HasPosLeadingCoeff g.derivative.derivative ∧
      g.derivative.derivative.natDegree = f.derivative.derivative.natDegree :=
  hfg.derivative_bundle_two hf hg hdeg.symm hpos

/-- Non-namespace wrapper for `PosComboRealRooted.derivative_bundle_two`. -/
theorem posComboRealRooted_derivative_bundle_two
    {f g : ℝ[X]} (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) (hpos : 2 ≤ f.natDegree)
    (hfg : PosComboRealRooted f g) :
    PosComboRealRooted f.derivative.derivative g.derivative.derivative ∧
      HasPosLeadingCoeff f.derivative.derivative ∧
      HasPosLeadingCoeff g.derivative.derivative ∧
      g.derivative.derivative.natDegree = f.derivative.derivative.natDegree :=
  hfg.derivative_bundle_two hf hg hdeg hpos

/-- Closed-interval preservation for a derivative pair. -/
theorem roots_derivative_mem_Icc_of_roots_mem_Icc_pair {f g : ℝ[X]} {u v : ℝ}
    (hf : f.Splits) (hg : g.Splits)
    (hfdeg : 2 ≤ f.natDegree) (hgdeg : 2 ≤ g.natDegree)
    (hfr : ∀ r ∈ f.roots, r ∈ Set.Icc u v)
    (hgr : ∀ r ∈ g.roots, r ∈ Set.Icc u v) :
    (∀ r ∈ f.derivative.roots, r ∈ Set.Icc u v) ∧
      (∀ r ∈ g.derivative.roots, r ∈ Set.Icc u v) :=
  ⟨roots_derivative_mem_Icc_of_roots_mem_Icc hf hfdeg hfr,
    roots_derivative_mem_Icc_of_roots_mem_Icc hg hgdeg hgr⟩

/-- Open-interval preservation for a derivative pair. -/
theorem roots_derivative_mem_Ioo_of_roots_mem_Ioo_pair {f g : ℝ[X]} {u v : ℝ}
    (hf : f.Splits) (hg : g.Splits)
    (hfdeg : 2 ≤ f.natDegree) (hgdeg : 2 ≤ g.natDegree)
    (hfr : ∀ r ∈ f.roots, r ∈ Set.Ioo u v)
    (hgr : ∀ r ∈ g.roots, r ∈ Set.Ioo u v) :
    (∀ r ∈ f.derivative.roots, r ∈ Set.Ioo u v) ∧
      (∀ r ∈ g.derivative.roots, r ∈ Set.Ioo u v) :=
  ⟨roots_derivative_mem_Ioo_of_roots_mem_Ioo hf hfdeg hfr,
    roots_derivative_mem_Ioo_of_roots_mem_Ioo hg hgdeg hgr⟩

/-- Closed lower-ray preservation for a derivative pair. -/
theorem roots_derivative_mem_Ici_of_roots_mem_Ici_pair {f g : ℝ[X]} {u : ℝ}
    (hf : f.Splits) (hg : g.Splits)
    (hfdeg : 2 ≤ f.natDegree) (hgdeg : 2 ≤ g.natDegree)
    (hfr : ∀ r ∈ f.roots, r ∈ Set.Ici u)
    (hgr : ∀ r ∈ g.roots, r ∈ Set.Ici u) :
    (∀ r ∈ f.derivative.roots, r ∈ Set.Ici u) ∧
      (∀ r ∈ g.derivative.roots, r ∈ Set.Ici u) :=
  ⟨roots_derivative_mem_Ici_of_roots_mem_Ici hf hfdeg hfr,
    roots_derivative_mem_Ici_of_roots_mem_Ici hg hgdeg hgr⟩

/-- Closed upper-ray preservation for a derivative pair. -/
theorem roots_derivative_mem_Iic_of_roots_mem_Iic_pair {f g : ℝ[X]} {v : ℝ}
    (hf : f.Splits) (hg : g.Splits)
    (hfdeg : 2 ≤ f.natDegree) (hgdeg : 2 ≤ g.natDegree)
    (hfr : ∀ r ∈ f.roots, r ∈ Set.Iic v)
    (hgr : ∀ r ∈ g.roots, r ∈ Set.Iic v) :
    (∀ r ∈ f.derivative.roots, r ∈ Set.Iic v) ∧
      (∀ r ∈ g.derivative.roots, r ∈ Set.Iic v) :=
  ⟨roots_derivative_mem_Iic_of_roots_mem_Iic hf hfdeg hfr,
    roots_derivative_mem_Iic_of_roots_mem_Iic hg hgdeg hgr⟩

/-- Closed-interval preservation across two differentiations. -/
theorem roots_iterate_derivative_two_mem_Icc_of_roots_mem_Icc {p : ℝ[X]} {u v : ℝ}
    (hp : p.Splits) (hdeg : 3 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ∈ Set.Icc u v) :
    ∀ r ∈ p.derivative.derivative.roots, r ∈ Set.Icc u v := by
  have hder_splits : p.derivative.Splits :=
    splits_derivative_of_two_le_natDegree hp (by lia)
  have hder_deg : 2 ≤ p.derivative.natDegree := by
    rw [p.natDegree_derivative]
    lia
  exact roots_derivative_mem_Icc_of_roots_mem_Icc hder_splits hder_deg
    (roots_derivative_mem_Icc_of_roots_mem_Icc hp (by lia) h)

/-- Open-interval preservation across two differentiations. -/
theorem roots_iterate_derivative_two_mem_Ioo_of_roots_mem_Ioo {p : ℝ[X]} {u v : ℝ}
    (hp : p.Splits) (hdeg : 3 ≤ p.natDegree)
    (h : ∀ r ∈ p.roots, r ∈ Set.Ioo u v) :
    ∀ r ∈ p.derivative.derivative.roots, r ∈ Set.Ioo u v := by
  have hder_splits : p.derivative.Splits :=
    splits_derivative_of_two_le_natDegree hp (by lia)
  have hder_deg : 2 ≤ p.derivative.natDegree := by
    rw [p.natDegree_derivative]
    lia
  exact roots_derivative_mem_Ioo_of_roots_mem_Ioo hder_splits hder_deg
    (roots_derivative_mem_Ioo_of_roots_mem_Ioo hp (by lia) h)

end RealRooted
