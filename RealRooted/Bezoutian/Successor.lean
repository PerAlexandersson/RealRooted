import RealRooted.Bezoutian
import RealRooted.Interlacing.Multiplicity
import RealRooted.Wronskian.Forward
import RealRooted.Wronskian.Successor.Interlacing

/-!
# Successor-degree Bézout criterion

For `f` of degree `d + 1` and `g` of degree `d`, both with positive leading
coefficients, the Bézout matrix `bezoutMatrix (d + 1) f g` is positive definite
if and only if `g` interlaces `f` with no common root (Fisk, *Polynomials,
roots, and interlacing*, Cor. 9.145).

The forward direction diagonalizes the Bézout matrix by the Vandermonde matrix
at the roots of `f`; the diagonal entries are the Wronskian values `f'(r) g(r)`.
The converse uses the positivity of the Wronskian `f' g - f g'` forced by a
positive definite Bézout matrix.
-/

open Polynomial Matrix

namespace RealRooted

/-- A real polynomial without complex roots in the open upper half-plane splits. -/
private lemma splits_of_no_upper_root {p : ℝ[X]}
    (h : ∀ z : ℂ, 0 < z.im → (p.map Complex.ofRealHom).eval z = 0 → False) :
    p.Splits := by
  refine Polynomial.splits_of_all_roots_real fun z hz ↦ ?_
  by_contra h_im
  rcases lt_or_gt_of_ne h_im with h_neg | h_pos
  · refine h (starRingEnd ℂ z) (by simp [h_neg]) ?_
    simpa [eval_eq_sum_range] using congr_arg Star.star hz
  · exact h z h_pos hz

/-- A positive definite successor-degree Bézout matrix forces both polynomials to
split. -/
theorem bezoutMatrix.splits_of_posDef_succ {f g : ℝ[X]} {d : ℕ}
    (hf_deg : f.natDegree = d + 1) (hg_deg : g.natDegree = d)
    (hB : (bezoutMatrix (d + 1) f g).PosDef) :
    f.Splits ∧ g.Splits :=
  ⟨splits_of_no_upper_root fun z hz hroot ↦ bezoutMatrix.no_complex_root_q_of_posDef
      (by lia) hf_deg.le hB z hz hroot,
    splits_of_no_upper_root fun z hz hroot ↦ bezoutMatrix.no_complex_root_of_posDef
      (by lia) hf_deg.le hB z hz hroot⟩

/-- A positive definite successor-degree Bézout matrix makes `g`
interlace `f` with no common root. -/
theorem bezoutMatrix.interlaces_of_posDef_succ {f g : ℝ[X]} {d : ℕ}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_deg : f.natDegree = d + 1) (hg_deg : g.natDegree = d)
    (hB : (bezoutMatrix (d + 1) f g).PosDef) :
    Interlaces g f ∧ ∀ x, f.IsRoot x → ¬ g.IsRoot x := by
  have hW := bezoutMatrix.wronskian_pos_of_posDef hf_deg.le (by lia) hB
  obtain ⟨hf_splits, hg_splits⟩ := bezoutMatrix.splits_of_posDef_succ hf_deg hg_deg hB
  refine ⟨interlaces_of_wronskian_neg_succ hg_pos hf_pos hg_deg hf_deg hg_splits hf_splits
    fun t ↦ by linarith [hW t], fun x hf hg ↦ ?_⟩
  have := hW x
  simp_all

/-- Interlacing without common roots forces simple roots. -/
theorem Interlaces.roots_nodup_of_disjoint {g f : ℝ[X]} (h : Interlaces g f)
    (hdisj : ∀ x, f.IsRoot x → ¬ g.IsRoot x) :
    f.roots.Nodup ∧ g.roots.Nodup := by
  constructor
  · by_contra hnd
    obtain ⟨r, hrf, hrg⟩ := exists_common_root_of_not_nodup h.toStrictInterl hnd
    exact hdisj r (isRoot_of_mem_roots hrf) (isRoot_of_mem_roots hrg)
  · by_contra hnd
    obtain ⟨r, hrf, hrg⟩ := exists_common_root_of_not_nodup_g h.toStrictInterl hnd
    exact hdisj r (isRoot_of_mem_roots hrf) (isRoot_of_mem_roots hrg)

/-- If `g` interlaces `f` with no common root, the successor-degree
Bézout matrix is positive definite. -/
theorem bezoutMatrix.posDef_of_interlaces_succ {f g : ℝ[X]} {d : ℕ}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_deg : f.natDegree = d + 1) (hg_deg : g.natDegree = d)
    (h : Interlaces g f) (hdisj : ∀ x, f.IsRoot x → ¬ g.IsRoot x) :
    (bezoutMatrix (d + 1) f g).PosDef := by
  obtain ⟨hf_nodup, hg_nodup⟩ := h.roots_nodup_of_disjoint hdisj
  obtain ⟨s, hs_mono, hs_roots⟩ :
      ∃ s : Fin (d + 1) → ℝ, StrictMono s ∧ ∀ k, f.IsRoot (s k) :=
    Polynomial.exists_strictMono_roots h.1.2 hf_deg hf_nodup
  have h_v_eq : vandermonde s * bezoutMatrix (d + 1) f g * (vandermonde s)ᵀ =
      diagonal fun k ↦ f.derivative.eval (s k) * g.eval (s k) := by
    have h_neg : bezoutMatrix (d + 1) f g = -bezoutMatrix (d + 1) g f := by
      ext i j
      simp [bezoutMatrix, bezoutEntry]
    convert congr_arg (fun x ↦ -x)
      (bezoutMatrix.vandermonde_eq_diagonal g f (d + 1) s (by lia) hf_deg.le
        (by simp_all) hs_mono.injective) using 1 <;> simp_all [mul_comm]
  refine Matrix.PosDef.of_congruent_to_diagonal ?_ ?_ h_v_eq
  · intro k
    have hW := wronskian_pos_of_strictInterl_succ hf_pos hg_pos (by lia) h.toStrictInterl
      hf_nodup hg_nodup hdisj (s k)
    have hf_zero : f.eval (s k) = 0 := hs_roots k
    simp_all
  · simp_all [Matrix.det_vandermonde, Finset.prod_eq_zero_iff, sub_eq_zero,
      hs_mono.injective.eq_iff]

/-- **Successor-degree Bézout criterion** (Fisk, Cor. 9.145). -/
theorem bezoutMatrix_posDef_iff_interlaces_succ {f g : ℝ[X]} {d : ℕ}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_deg : f.natDegree = d + 1) (hg_deg : g.natDegree = d) :
    (bezoutMatrix (d + 1) f g).PosDef ↔
      Interlaces g f ∧ ∀ x, f.IsRoot x → ¬ g.IsRoot x :=
  ⟨bezoutMatrix.interlaces_of_posDef_succ hf_pos hg_pos hf_deg hg_deg,
    fun h ↦ bezoutMatrix.posDef_of_interlaces_succ hf_pos hg_pos hf_deg hg_deg h.1 h.2⟩

end RealRooted
