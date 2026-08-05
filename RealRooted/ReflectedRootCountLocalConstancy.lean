import RealRooted.DegreeDropReversal
import RealRooted.Linear
import RealRooted.PositiveParameterLocalLowerCount

/-!
# Root-count local constancy through degree drops

Reflection at a common degree bound turns a possible leading-degree drop into
zero-root padding.  When the original affine family is nonzero at the left
endpoint of a positive interval, the reflected family therefore has constant
degree, so the existing analytic local-constancy theorem applies.
-/

open Polynomial

namespace RealRooted

open DegreeDropReversal

/-- Root counts in `(0, b)` are constant along a split affine family when the
family stays nonzero at both interval endpoints, even if its degree drops. -/
theorem rightFamily_card_roots_Ioo_zero_eq_zero_param_of_degree_bound
    {f g : ℝ[X]} {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) {N : ℕ}
    (hN : ∀ η ∈ Set.Icc (0 : ℝ) μ, (f + C η * g).natDegree ≤ N)
    (hzero : ∀ η ∈ Set.Icc (0 : ℝ) μ, (f + C η * g).coeff 0 ≠ 0)
    (hsplit : ∀ η ∈ Set.Icc (0 : ℝ) μ, (f + C η * g).Splits)
    (hbroot : ∀ η ∈ Set.Icc (0 : ℝ) μ, ¬ (f + C η * g).IsRoot b) :
    ((f + C μ * g).roots.filter (fun r ↦ 0 < r ∧ r < b)).card =
      (f.roots.filter (fun r ↦ 0 < r ∧ r < b)).card := by
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) μ := ⟨le_rfl, hμ.le⟩
  have hμ_mem : μ ∈ Set.Icc (0 : ℝ) μ := ⟨hμ.le, le_rfl⟩
  have hfN : f.natDegree ≤ N := by
    simpa using hN 0 hzero_mem
  have hfzero : f.coeff 0 ≠ 0 := by
    simpa using hzero 0 hzero_mem
  have hf_split : f.Splits := by
    simpa using hsplit 0 hzero_mem
  have hreflect_degree : ∀ η ∈ Set.Icc (0 : ℝ) μ,
      (reflect N f + C η * reflect N g).natDegree =
        (reflect N f + C (0 : ℝ) * reflect N g).natDegree := by
    intro η hη
    calc
      (reflect N f + C η * reflect N g).natDegree =
          (reflect N (f + C η * g)).natDegree := by rw [reflect_add_C_mul]
      _ = N := natDegree_reflect_eq_of_coeff_zero_ne (hN η hη) (hzero η hη)
      _ = (reflect N f).natDegree :=
        (natDegree_reflect_eq_of_coeff_zero_ne hfN hfzero).symm
      _ = (reflect N f + C (0 : ℝ) * reflect N g).natDegree := by simp
  have hreflect_split : ∀ η ∈ Set.Icc (0 : ℝ) μ,
      (reflect N f + C η * reflect N g).Splits := by
    intro η hη
    rw [← reflect_add_C_mul]
    exact splits_reflect_of_splits (hsplit η hη) (hN η hη)
  have hreflect_not_root : ∀ η ∈ Set.Icc (0 : ℝ) μ,
      ¬ (reflect N f + C η * reflect N g).IsRoot b⁻¹ := by
    intro η hη
    rw [← reflect_add_C_mul]
    exact (not_congr (isRoot_reflect_inv_iff hb.ne' (hN η hη))).mpr
      (hbroot η hη)
  have hreflect_count :=
    rightFamily_card_roots_gt_eq_zero_param_of_constant_degree
      (f := reflect N f) (g := reflect N g) (x := b⁻¹) (hμ_pos := hμ)
      hreflect_degree hreflect_split hreflect_not_root
  have hcount :
      ((reflect N (f + C μ * g)).roots.filter (b⁻¹ < ·)).card =
        ((reflect N f).roots.filter (b⁻¹ < ·)).card := by
    simpa only [reflect_add_C_mul] using hreflect_count
  have hμ_transport := card_roots_reflect_Ioi
    (p := f + C μ * g) (hsplit μ hμ_mem) (hzero μ hμ_mem)
    (hN μ hμ_mem) (a := b⁻¹) (inv_pos.mpr hb)
  have hf_transport := card_roots_reflect_Ioi
    (p := f) hf_split hfzero hfN (a := b⁻¹) (inv_pos.mpr hb)
  calc
    ((f + C μ * g).roots.filter (fun r ↦ 0 < r ∧ r < b)).card =
        ((reflect N (f + C μ * g)).roots.filter (b⁻¹ < ·)).card := by
          simpa using hμ_transport.symm
    _ = ((reflect N f).roots.filter (b⁻¹ < ·)).card := hcount
    _ = (f.roots.filter (fun r ↦ 0 < r ∧ r < b)).card := by
      simpa using hf_transport

/-- Root counts in any bounded open interval are constant along a split affine
family whose interval endpoints stay root-free, even if its degree drops. -/
theorem rightFamily_card_roots_Ioo_eq_zero_param_of_degree_bound
    {f g : ℝ[X]} {a b μ : ℝ} (hab : a < b) (hμ : 0 < μ) {N : ℕ}
    (hN : ∀ η ∈ Set.Icc (0 : ℝ) μ, (f + C η * g).natDegree ≤ N)
    (haroot : ∀ η ∈ Set.Icc (0 : ℝ) μ, ¬ (f + C η * g).IsRoot a)
    (hsplit : ∀ η ∈ Set.Icc (0 : ℝ) μ, (f + C η * g).Splits)
    (hbroot : ∀ η ∈ Set.Icc (0 : ℝ) μ, ¬ (f + C η * g).IsRoot b) :
    ((f + C μ * g).roots.filter (fun r ↦ a < r ∧ r < b)).card =
      (f.roots.filter (fun r ↦ a < r ∧ r < b)).card := by
  let f' := f.comp (X + C a)
  let g' := g.comp (X + C a)
  have hfamily_comp (eta : ℝ) :
      f' + C eta * g' = (f + C eta * g).comp (X + C a) := by
    simp [f', g', Polynomial.add_comp, Polynomial.mul_comp]
  have hN' : ∀ eta ∈ Set.Icc (0 : ℝ) μ, (f' + C eta * g').natDegree ≤ N := by
    intro eta heta
    rw [hfamily_comp, Polynomial.natDegree_comp]
    simpa using hN eta heta
  have hzero' : ∀ eta ∈ Set.Icc (0 : ℝ) μ, (f' + C eta * g').coeff 0 ≠ 0 := by
    intro eta heta
    rw [hfamily_comp]
    simpa [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp] using
      haroot eta heta
  have hsplit' : ∀ eta ∈ Set.Icc (0 : ℝ) μ, (f' + C eta * g').Splits := by
    intro eta heta
    rw [hfamily_comp]
    exact (hsplit eta heta).comp_X_add_C a
  have hbroot' : ∀ eta ∈ Set.Icc (0 : ℝ) μ,
      ¬ (f' + C eta * g').IsRoot (b - a) := by
    intro eta heta
    rw [hfamily_comp]
    intro hroot
    apply hbroot eta heta
    change eval b (f + C eta * g) = 0
    change eval (b - a) ((f + C eta * g).comp (X + C a)) = 0 at hroot
    simpa [Polynomial.eval_comp] using hroot
  have hshifted := rightFamily_card_roots_Ioo_zero_eq_zero_param_of_degree_bound
    (f := f') (g := g') (b := b - a) (sub_pos.mpr hab) hμ
    hN' hzero' hsplit' hbroot'
  have htop := card_roots_comp_X_add_C_Ioo (f + C μ * g) a b
  have hbase := card_roots_comp_X_add_C_Ioo f a b
  calc
    ((f + C μ * g).roots.filter (fun r ↦ a < r ∧ r < b)).card =
        (((f + C μ * g).comp (X + C a)).roots.filter
          (fun r ↦ 0 < r ∧ r < b - a)).card := htop.symm
    _ = ((f' + C μ * g').roots.filter (fun r ↦ 0 < r ∧ r < b - a)).card := by
      rw [hfamily_comp]
    _ = (f'.roots.filter (fun r ↦ 0 < r ∧ r < b - a)).card := hshifted
    _ = (f.roots.filter (fun r ↦ a < r ∧ r < b)).card := hbase

/-- Root counts in a bounded open interval are constant along a split affine
family whose endpoints stay root-free, with the common degree bound inferred
from the two endpoint polynomials. -/
theorem rightFamily_card_roots_Ioo_eq_zero_param
    {f g : ℝ[X]} {a b μ : ℝ} (hab : a < b) (hμ : 0 < μ)
    (haroot : ∀ η ∈ Set.Icc (0 : ℝ) μ, ¬ (f + C η * g).IsRoot a)
    (hsplit : ∀ η ∈ Set.Icc (0 : ℝ) μ, (f + C η * g).Splits)
    (hbroot : ∀ η ∈ Set.Icc (0 : ℝ) μ, ¬ (f + C η * g).IsRoot b) :
    ((f + C μ * g).roots.filter (fun r ↦ a < r ∧ r < b)).card =
      (f.roots.filter (fun r ↦ a < r ∧ r < b)).card := by
  apply rightFamily_card_roots_Ioo_eq_zero_param_of_degree_bound
    (N := max f.natDegree g.natDegree) hab hμ
  · intro η _
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (le_max_left _ _)
        ((Polynomial.natDegree_C_mul_le η g).trans (le_max_right _ _)))
  · exact haroot
  · exact hsplit
  · exact hbroot

end RealRooted
