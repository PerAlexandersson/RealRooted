import RealRooted.Tactic.InterlacingSequence

open Polynomial

namespace RealRooted
namespace Tactic

example {fs : List ℝ[X]} :
    IsInterlacingSeq fs ↔ fs.Pairwise Prec := by
  rr_interlacingSeq_iff_pairwise

example {fs : List ℝ[X]} :
    IsInterlacingSeq0 fs ↔ fs.Pairwise Prec0 := by
  rr_interlacingSeq0_iff_pairwise

example {fs : List ℝ[X]}
    (hfs : IsInterlacingSeq fs) :
    IsInterlacingSeq0 fs := by
  rr_interlacingSeq_to_interlacingSeq0 using interlacing := hfs

example {fs : List ℝ[X]} {i j : Fin fs.length}
    (hfs : IsInterlacingSeq fs)
    (hij : i < j) :
    Prec (fs.get i) (fs.get j) := by
  rr_interlacingSeq_prec using interlacing := hfs, index_lt := hij

example {fs : List ℝ[X]} {i j : Fin fs.length}
    (hfs : IsInterlacingSeq0 fs)
    (hij : i < j) :
    Prec0 (fs.get i) (fs.get j) := by
  rr_interlacingSeq0_prec0 using interlacing0 := hfs, index_lt := hij

example {fs gs : List ℝ[X]}
    (hfs : IsInterlacingSeq fs)
    (hgs : gs.Sublist fs) :
    IsInterlacingSeq gs := by
  rr_interlacingSeq_sublist using interlacing := hfs, sublist := hgs

example {fs gs : List ℝ[X]}
    (hfs : IsInterlacingSeqNonneg fs)
    (hgs : gs.Sublist fs) :
    IsInterlacingSeqNonneg gs := by
  rr_interlacingSeqNonneg_sublist using
    interlacing_nonneg := hfs,
    sublist := hgs

example {fs gs : List ℝ[X]}
    (hfs : IsInterlacingSeq0 fs)
    (hgs : gs.Sublist fs) :
    IsInterlacingSeq0 gs := by
  rr_interlacingSeq0_sublist using interlacing0 := hfs, sublist := hgs

example {fs gs : List ℝ[X]}
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hgs : gs.Sublist fs)
    (hreal : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hne : ∀ f ∈ gs, f ≠ 0) :
    IsInterlacingSeqNonneg gs := by
  rr_interlacingSeq0Nonneg_sublist_realrooted using
    interlacing0_nonneg := hfs,
    sublist := hgs,
    realrooted := hreal,
    nonzero := hne

example {fs gs : List ℝ[X]}
    (hfs : IsInterlacingSeq fs)
    (hgs : IsInterlacingSeq gs)
    (hfg : ∀ f ∈ fs, ∀ g ∈ gs, Prec f g) :
    IsInterlacingSeq (fs ++ gs) := by
  rr_interlacingSeq_append using
    left_interlacing := hfs,
    right_interlacing := hgs,
    cross_prec := hfg

example {fs : List ℝ[X]}
    (hfs : IsInterlacingSeq fs) :
    fs.reverse.Pairwise (fun f g => Prec g f) := by
  rr_interlacingSeq_reverse_pairwise using interlacing := hfs

example {fs : List ℝ[X]}
    (hfs : IsInterlacingSeq0 fs) :
    fs.reverse.Pairwise (fun f g => Prec0 g f) := by
  rr_interlacingSeq0_reverse_pairwise using interlacing0 := hfs

example {fs : List ℝ[X]}
    (hfs : IsInterlacingSeqNonneg fs) :
    (∀ f ∈ fs.reverse, (f ≠ 0 ∧ f.Splits) ∧ HasNonnegCoeffs f) ∧
      fs.reverse.Pairwise (fun f g => Prec g f) := by
  rr_interlacingSeqNonneg_reverse_pairwise using interlacing_nonneg := hfs

example {fs : List ℝ[X]}
    (hfs : IsInterlacingSeqNonneg fs) :
    ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits) := by
  rr_interlacingSeqNonneg_realrooted using interlacing_nonneg := hfs

example {fs : List ℝ[X]} {f : ℝ[X]}
    (hfs : IsInterlacingSeqNonneg fs)
    (hf : f ∈ fs) :
    f.Splits := by
  rr_interlacingSeqNonneg_splits using
    interlacing_nonneg := hfs,
    member := hf

example {fs : List ℝ[X]}
    (hfs : IsInterlacingSeqNonneg fs) :
    ∀ f ∈ fs, HasPosLeadingCoeff f := by
  rr_interlacingSeqNonneg_pos_lc using interlacing_nonneg := hfs

example {fs : List ℝ[X]}
    (hfs : IsInterlacingSeqNonneg fs) :
    ∀ f ∈ fs, HasNonnegCoeffs f := by
  rr_interlacingSeqNonneg_nonneg_coeffs using interlacing_nonneg := hfs

example {fs : List ℝ[X]}
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hreal : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeqNonneg (fs.filter (· ≠ 0)) := by
  rr_interlacingSeq0Nonneg_filter_ne_zero using
    interlacing0_nonneg := hfs,
    realrooted := hreal

end Tactic
end RealRooted
