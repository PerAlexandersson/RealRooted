import RealRooted.Tactic.StaircaseSum

open Polynomial

namespace RealRooted
namespace Tactic

example (fs : List ℝ[X]) :
    staircaseSum fs 0 = fs.sum := by
  rr_staircaseSum_zero

example {FS : Nat → List ℝ[X]} :
    ∀ i : Nat, staircaseSum (FS i) 0 = (FS i).sum := by
  rr_staircaseSum_sequence_zero

example (fs : List ℝ[X]) :
    staircaseSum fs fs.length = X * fs.sum := by
  rr_staircaseSum_length

example {FS : Nat → List ℝ[X]} :
    ∀ i : Nat, staircaseSum (FS i) (FS i).length = X * (FS i).sum := by
  rr_staircaseSum_sequence_length

example {fs : List ℝ[X]} {m : Nat}
    (hfs : IsInterlacingSeqNonneg fs)
    (hm : m < fs.length) :
    Prec (fs.get ⟨m, hm⟩) (staircaseSum fs m) := by
  rr_staircaseSum_prec using interlacing_nonneg := hfs, index_lt := hm

example {FS : Nat → List ℝ[X]} {M : Nat → Nat}
    (hFS : ∀ i : Nat, IsInterlacingSeqNonneg (FS i))
    (hM : ∀ i : Nat, M i < (FS i).length) :
    ∀ i : Nat, Prec ((FS i).get ⟨M i, hM i⟩) (staircaseSum (FS i) (M i)) := by
  rr_staircaseSum_sequence_prec using interlacing_nonneg := hFS, index_lt := hM

example {fs : List ℝ[X]} {m : Nat}
    (hfs : IsInterlacingSeqNonneg fs)
    (hm : m < fs.length) :
    (staircaseSum fs m) ≠ 0 ∧ (staircaseSum fs m).Splits := by
  rr_staircaseSum_realrooted using interlacing_nonneg := hfs, index_lt := hm

example {FS : Nat → List ℝ[X]} {M : Nat → Nat}
    (hFS : ∀ i : Nat, IsInterlacingSeqNonneg (FS i))
    (hM : ∀ i : Nat, M i < (FS i).length) :
    ∀ i : Nat, staircaseSum (FS i) (M i) ≠ 0 ∧
      (staircaseSum (FS i) (M i)).Splits := by
  rr_staircaseSum_sequence_realrooted using
    interlacing_nonneg := hFS,
    index_lt := hM

end Tactic
end RealRooted
